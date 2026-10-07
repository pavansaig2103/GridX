// GRIDLOCK-X - Adaptive Urban Traffic Control & Emergency Routing Engine
// A self-contained college C++17 / DSA project.
// Build: g++ -std=c++17 GRIDLOCK_X.cpp -o gridlock
// Run: gridlock.exe | --demo | --demo-compare | --self-test
// Contribution 1 is deliberately the largest: it owns both manual ADTs,
// the simulation, emergency movement, rerouting and session integration.

// ============================================================
// LIBRARIES - standard C++17 only
// ============================================================
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <iomanip>
#include <iostream>     
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace std;

// ============================================================
// CONSTANTS
// ============================================================
constexpr int ROWS = 3, COLS = 3, INTERSECTIONS = 9;
constexpr int TOTAL_CYCLES = 20, LANE_CAPACITY = 50, PLAN_CAPACITY = 20;
constexpr int GREEN_LIMIT = 2, CYCLE_SECONDS = 10;
constexpr int SIGNIFICANT_QUEUE_CHANGE = 4, MAX_TRAFFIC_RESULTS = 3;
enum Lane { NORTH = 0, SOUTH = 1, EAST = 2, WEST = 3 };
const string NS_GREEN = "NS_GREEN", EW_GREEN = "EW_GREEN";
const string BORDER(50, '=');

// ============================================================
// CONTRIBUTION 4 - 15%: STRUCTURES & STRING PROCESSING
// ============================================================
struct Vehicle {
    int id = 0;
    string type = "CAR";
    int waitingTime = 0;
    int priority = 1;
    char destination = 'X'; // X means leave the network after this crossing.
    string route;          // A short, predefined route; no pathfinding.
    int routePosition = 0;
};

struct Incident {
    int cycle;
    string type;
    char location;
    string description;
};

struct SignalPlan {
    string signals[INTERSECTIONS];
    int detourChoice = 0; // Operator road control, not physical accident state.
    int savedCycle = -1;
};

struct PerformanceReport {
    int vehiclesProcessed = 0, vehiclesArrived = 0, vehiclesRejected = 0;
    int emergencyCleared = 0, emergencyTotal = 0, gridlockEvents = 0;
    int signalChanges = 0, cyclesCompleted = 0, vehiclesRemaining = 0;
    double averageWaiting = 0, peakCongestion = 0;
    double trafficFlow = 0, waitingPerformance = 0, emergencyResponse = 0;
    double congestionControl = 0, signalEfficiency = 0, efficiencyIndex = 0;
};

struct EmergencyRequest {
    int vehicleId = 0, enteredCycle = 0, clearedCycle = 0;
    int blockedCycles = 0, priorityUntil = 0;
    char location = 'D';
    int lane = WEST;
    string label, route;
    int routePosition = 0;
    bool cleared = false, movedThisCycle = false;
};

struct ParsedCommand {
    string action, value;
    char intersection = '\0';
    bool valid = false;
};

// A recommendation describes an existing action; it never changes traffic
// until the operator selects APPLY. No AI, external data or new engine rules.
enum RecommendationAction { RECOMMEND_EMERGENCY, RECOMMEND_DETOUR,
                            RECOMMEND_SIGNAL, RECOMMEND_NEXT };
constexpr int MAX_RECOMMENDATIONS = INTERSECTIONS + 3;
struct TrafficRecommendation {
    RecommendationAction action = RECOMMEND_NEXT;
    int intersection = -1, emergency = -1, detour = 0;
    string signal;
    int expectedVehicles = 0, queueDifference = 0;
};

string normalize(string text) {
    size_t start = text.find_first_not_of(" \t\r\n");
    if (start == string::npos) return "";
    size_t end = text.find_last_not_of(" \t\r\n");
    text = text.substr(start, end - start + 1);
    for (char& ch : text)
        ch = static_cast<char>(toupper(static_cast<unsigned char>(ch)));
    return text;
}

// find(), substr(), comparisons and uppercase normalization demonstrate
// string processing. Commands are optional; all gameplay has numbered menus.
ParsedCommand parseCommand(const string& input) {
    ParsedCommand command;
    string text = normalize(input);
    size_t first = text.find(':');
    if (first == string::npos) return command;
    command.action = text.substr(0, first);
    string rest = text.substr(first + 1);
    if (command.action == "SIGNAL") {
        size_t second = rest.find(':');
        if (second != 1 || rest[0] < 'A' || rest[0] > 'I') return command;
        command.intersection = rest[0];
        command.value = rest.substr(second + 1);
        command.valid = command.value == "NS" || command.value == "EW";
    } else if (command.action == "INSPECT") {
        command.valid = rest.size() == 1 && rest[0] >= 'A' && rest[0] <= 'I';
        if (command.valid) command.intersection = rest[0];
    } else if (command.action == "EMERGENCY") {
        command.valid = rest == "PRIORITIZE";
    } else if (command.action == "SAVE" || command.action == "RESTORE") {
        command.valid = rest == "PLAN";
    }
    return command;
}

// ============================================================
// CONTRIBUTION 1 - 40%: MANUAL ARRAY-BASED CIRCULAR QUEUE
// ============================================================
class VehicleQueue {
private:
    Vehicle data[LANE_CAPACITY];
    int frontIndex = 0, rearIndex = 0, count = 0;
public:
    bool isEmpty() const { return count == 0; }
    bool isFull() const { return count == LANE_CAPACITY; }
    int size() const { return count; }

    // O(1): no shifting. Returning false protects a full queue.
    bool enqueue(const Vehicle& vehicle) {
        if (isFull()) return false;
        data[rearIndex] = vehicle;
        rearIndex = (rearIndex + 1) % LANE_CAPACITY;
        ++count;
        return true;
    }

    // O(1): modulo wraps the head. id == 0 is the empty sentinel.
    Vehicle dequeue() {
        if (isEmpty()) return Vehicle{};
        Vehicle result = data[frontIndex];
        frontIndex = (frontIndex + 1) % LANE_CAPACITY;
        --count;
        return result;
    }

    Vehicle peek() const { return isEmpty() ? Vehicle{} : data[frontIndex]; }

    // Waiting updates visit every queued vehicle without changing FIFO order.
    // Valid offset access is O(1); the caller loops from 0 to size()-1.
    Vehicle& at(int offset) { return data[(frontIndex + offset) % LANE_CAPACITY]; }
    const Vehicle& at(int offset) const {
        return data[(frontIndex + offset) % LANE_CAPACITY];
    }
};

// ============================================================
// CONTRIBUTION 3 - 15%: CITY GRID & INTERSECTION MATRIX
// ============================================================
struct Intersection {
    char name = 'A';
    string signalState = NS_GREEN;
    VehicleQueue north, south, east, west;
    int vehiclesPassed = 0, totalWaitingTime = 0, congestionLevel = 0;
    bool signalOperational = true;
};

VehicleQueue& laneQueue(Intersection& intersection, int lane) {
    if (lane == NORTH) return intersection.north;
    if (lane == SOUTH) return intersection.south;
    if (lane == EAST) return intersection.east;
    return intersection.west;
}
const VehicleQueue& laneQueue(const Intersection& intersection, int lane) {
    if (lane == NORTH) return intersection.north;
    if (lane == SOUTH) return intersection.south;
    if (lane == EAST) return intersection.east;
    return intersection.west;
}
int queueTotal(const Intersection& intersection) {
    return intersection.north.size() + intersection.south.size()
         + intersection.east.size() + intersection.west.size();
}
bool northSouth(int lane) { return lane == NORTH || lane == SOUTH; }
string laneName(int lane) {
    const string names[4] = {"North", "South", "East", "West"};
    return names[lane];
}

struct CityGrid {
    Intersection city[ROWS][COLS]; // The required 2D array.

    CityGrid() {
        // O(R*C), or O(N^2) for a general N by N grid.
        for (int row = 0; row < ROWS; ++row)
            for (int col = 0; col < COLS; ++col) {
                Intersection& point = city[row][col];
                point.name = static_cast<char>('A' + row * COLS + col);
                point.signalState = (row + col) % 2 == 0 ? NS_GREEN : EW_GREEN;
            }
    }
    Intersection& at(int index) { return city[index / COLS][index % COLS]; }
    const Intersection& at(int index) const {
        return city[index / COLS][index % COLS];
    }
};

// A vehicle entering from NORTH normally travels toward the next row.
char straightDestination(int index, int lane) {
    int row = index / COLS, col = index % COLS;
    if (lane == NORTH) ++row;
    if (lane == SOUTH) --row;
    if (lane == EAST) --col;
    if (lane == WEST) ++col;
    if (row < 0 || row >= ROWS || col < 0 || col >= COLS) return 'X';
    return static_cast<char>('A' + row * COLS + col);
}

int incomingLane(char from, char to) {
    int delta = to - from;
    if (delta == COLS) return NORTH;
    if (delta == -COLS) return SOUTH;
    if (delta == 1) return WEST;
    return EAST;
}

void displayCity(const CityGrid& grid) {
    cout << "\nCITY:  name[green direction | vehicles waiting]\n\n";
    for (int row = 0; row < ROWS; ++row) {
        for (int col = 0; col < COLS; ++col) {
            const Intersection& point = grid.city[row][col];
            string signal = point.signalOperational
                ? (point.signalState == NS_GREEN ? "NS" : "EW") : "OFF";
            ostringstream cell;
            cell << point.name << '[' << signal << '|' << setfill('0')
                 << setw(2) << queueTotal(point) << ']';
            cout << left << setw(10) << cell.str();
            if (col < COLS - 1) cout << " -- ";
        }
        cout << '\n';
        if (row < ROWS - 1) cout << "    |             |             |\n";
    }
    cout << right << setfill(' ');
}

void displayCongestionMatrix(const CityGrid& grid) {
    cout << "\n3 x 3 CONGESTION MATRIX (%)\n";
    for (int row = 0; row < ROWS; ++row) {
        for (int col = 0; col < COLS; ++col)
            cout << grid.city[row][col].name << ':' << setw(3)
                 << grid.city[row][col].congestionLevel << "%  ";
        cout << '\n';
    }
    cout << "Each cell: min(100, waiting vehicles / 15 * 100).\n";
}

// ============================================================
// CONTRIBUTION 2 - 15%: 1D ARRAYS, TELEMETRY & TERMINAL INTERFACE
// ============================================================
struct Telemetry {
    // Index 0 = A, ... index 8 = I. Direct array access is O(1).
    int congestionLevels[INTERSECTIONS] = {};
    int vehiclesCleared[INTERSECTIONS] = {}; // Cumulative departures, including detours.
    int waitingTotals[INTERSECTIONS] = {};  // Cumulative vehicle-seconds.
    int signalChanges[INTERSECTIONS] = {};
    int emergencyDelays[INTERSECTIONS] = {};
    int gridlockStreak[INTERSECTIONS] = {};
    int changesThisCycle[INTERSECTIONS] = {};

    // This-cycle movement ledger. Reset before ANY arrivals each cycle.
    int queueAtCycleStart[INTERSECTIONS] = {};
    int externalArrivals[INTERSECTIONS] = {};
    int internalArrivals[INTERSECTIONS] = {};
    int vehiclesPassedSignal[INTERSECTIONS] = {};
    int networkExitsFromIntersection[INTERSECTIONS] = {};
    int queueAtCycleEnd[INTERSECTIONS] = {};
    // Diversions bypass the signal. Keep their source departures separate
    // so start + external + internal - green crossings - diversions = end.
    int divertedOut[INTERSECTIONS] = {};
};

struct DashboardMetrics {
    int cycle = 0, networkExits = 0, hotspot = 0;
    double flow = 0, wait = 0, congestion = 0;
    string emergencyStatus = "CLEAR";
    bool roadBlocked = false;
};

string trafficResultExplanation(const Telemetry& telemetry, int index) {
    int arrivals = telemetry.externalArrivals[index] + telemetry.internalArrivals[index];
    int passed = telemetry.vehiclesPassedSignal[index];
    int diverted = telemetry.divertedOut[index];
    int start = telemetry.queueAtCycleStart[index], end = telemetry.queueAtCycleEnd[index];
    ostringstream explanation;
    if (passed > 0) explanation << "The signal successfully moved " << passed
                               << (passed == 1 ? " vehicle" : " vehicles");
    else explanation << "No vehicles crossed the green signal";
    explanation << ",\nand " << arrivals << (arrivals == 1 ? " vehicle entered" : " vehicles entered")
                << " this intersection during the same cycle.\n";
    if (diverted > 0)
        explanation << "Another " << diverted << (diverted == 1 ? " vehicle left" : " vehicles left")
                    << " this queue via manual diversion.\n";
    if (end < start) explanation << "Traffic pressure fell by " << start - end
                               << (start - end == 1 ? " vehicle." : " vehicles.");
    else if (end > start)
        explanation << "Traffic pressure rose by " << end - start << ": arrivals outpaced departures.";
    else if (arrivals == 0 && passed == 0 && diverted == 0)
        explanation << "The waiting count stayed the same; no vehicles arrived or departed.";
    else explanation << "Traffic pressure stayed the same: arrivals matched departures.";
    return explanation.str();
}

void displayIntersectionTrafficResult(const CityGrid& grid, const Telemetry& telemetry, int index) {
    cout << "\nINTERSECTION " << grid.at(index).name << "\n\n"
         << "Started Waiting      : " << telemetry.queueAtCycleStart[index] << '\n'
         << "New City Arrivals    : +" << telemetry.externalArrivals[index] << '\n'
         << "Incoming From Roads  : +" << telemetry.internalArrivals[index] << '\n'
         << "Passed Green Signal  : -" << telemetry.vehiclesPassedSignal[index] << '\n'
         << "Network Exits        : " << telemetry.networkExitsFromIntersection[index]
         << " (included in green crossings)\n";
    if (telemetry.divertedOut[index] > 0)
        cout << "Manual Diversions    : -" << telemetry.divertedOut[index] << '\n';
    cout << string(32, '-') << "\nWaiting Now          : " << telemetry.queueAtCycleEnd[index]
         << "\n\nNET CHANGE: " << telemetry.queueAtCycleStart[index] << " -> "
         << telemetry.queueAtCycleEnd[index] << "\n\nRESULT:\n"
         << trafficResultExplanation(telemetry, index) << '\n';
    if (!grid.at(index).signalOperational && telemetry.vehiclesPassedSignal[index] == 0)
        cout << "The failed signal prevented green-lane movement.\n";
}

bool inputClosed = false;
bool readInput(string& input) {
    if (!getline(cin, input)) {
        inputClosed = true;
        return false;
    }
    input = normalize(input);
    return true;
}

int readMenu(int minimum, int maximum, const string& prompt = "Choice > ") {
    string input;
    while (!inputClosed) {
        cout << prompt;
        if (!readInput(input)) return -1;
        // No stoi(): even an extremely long invalid input cannot overflow.
        if (input.size() == 1 && input[0] >= '0' && input[0] <= '9') {
            int value = input[0] - '0';
            if (value >= minimum && value <= maximum) return value;
        }
        cout << "Enter a number from " << minimum << " to " << maximum << ".\n";
    }
    return -1;
}

bool confirm(const string& prompt) {
    string input;
    while (!inputClosed) {
        cout << prompt << " [Y/N] > ";
        if (!readInput(input)) return false;
        if (input == "Y" || input == "YES") return true;
        if (input == "N" || input == "NO") return false;
        cout << "Enter Y or N.\n";
    }
    return false;
}

int selectIntersection() {
    cout << "\nSELECT INTERSECTION\n";
    for (int i = 0; i < INTERSECTIONS; ++i)
        cout << i + 1 << ". " << static_cast<char>('A' + i) << '\n';
    string input;
    while (!inputClosed) {
        cout << "Choice > ";
        if (!readInput(input)) return -1;
        if (input.size() == 1) {
            if (input[0] >= '1' && input[0] <= '9') return input[0] - '1';
            if (input[0] >= 'A' && input[0] <= 'I') return input[0] - 'A';
        }
        cout << "Choose 1-9 (or A-I).\n";
    }
    return -1;
}

string congestionLabel(int waiting) {
    if (waiting <= 4) return "LOW";
    if (waiting <= 8) return "MODERATE";
    if (waiting <= 12) return "HIGH";
    return "GRIDLOCK RISK";
}

void displayDashboard(const CityGrid& grid, const DashboardMetrics& metrics,
                      const string& operatorName) {
    cout << '\n' << BORDER << "\nGRIDLOCK-X // CYCLE " << setfill('0')
         << setw(2) << metrics.cycle << " / 20 // " << operatorName
         << setfill(' ') << '\n' << BORDER << '\n';
    cout << fixed << setprecision(0)
         << "NETWORK FLOW      : " << metrics.flow << "%\n"
         << "AVG WAIT          : " << metrics.wait << " sec\n"
         << "CONGESTION        : " << metrics.congestion << "%\n"
         << "NETWORK EXITS     : " << metrics.networkExits << '\n'
         << "EMERGENCY STATUS  : " << metrics.emergencyStatus << '\n';
    if (metrics.roadBlocked) cout << "ROAD B-E          : BLOCKED (reroute with option 4)\n";
    if (!grid.at(4).signalOperational) cout << "SIGNAL E          : OFF; repair due cycle 19\n";
    displayCity(grid);
    const Intersection& hotspot = grid.at(metrics.hotspot);
    cout << "\nHOTSPOT: INTERSECTION " << hotspot.name << " - "
         << queueTotal(hotspot) << " waiting / "
         << congestionLabel(queueTotal(hotspot)) << "\n\n"
         << "1. GET RECOMMENDATION\n2. CHANGE SIGNAL\n3. PRIORITIZE EMERGENCY\n"
         << "4. REROUTE TRAFFIC\n5. SAVE SIGNAL PLAN\n6. RESTORE SIGNAL PLAN\n"
         << "7. INSPECT INTERSECTION\n8. MORE / DETAILS\n9. NEXT CYCLE\n";
    if (metrics.cycle == TOTAL_CYCLES) cout << "Next cycle opens the final assessment.\n";
}

// ============================================================
// CONTRIBUTION 5 - 15%: STL RECORDS & INTERSECTION LOOKUP
// (The analytics implementation appears after the core engine.)
// ============================================================
struct NetworkRecords {
    unordered_map<char, pair<int, int>> coordinates;
    vector<string> history;
    set<int> processedEmergencies;
    set<string> incidentCategories;

    NetworkRecords() {
        for (int i = 0; i < INTERSECTIONS; ++i)
            coordinates.emplace(static_cast<char>('A' + i), make_pair(i / COLS, i % COLS));
    }
    // O(1) average lookup; O(I) worst case for a hash collision chain.
    int indexOf(char name) const {
        auto found = coordinates.find(name);
        if (found == coordinates.end()) return -1;
        return found->second.first * COLS + found->second.second;
    }
    void log(int cycle, const string& category, const string& message) {
        ostringstream entry;
        entry << "CYCLE " << setfill('0') << setw(2) << cycle
              << " [" << category << "] " << message;
        history.push_back(entry.str());
    }
};

// ============================================================
// CONTRIBUTION 1 - 40%: MANUAL STACK & CORE SIMULATION ENGINE
// ============================================================
class SignalPlanStack {
private:
    SignalPlan plans[PLAN_CAPACITY];
    int topIndex = -1;
public:
    bool isEmpty() const { return topIndex == -1; }
    bool isFull() const { return topIndex == PLAN_CAPACITY - 1; }
    int size() const { return topIndex + 1; }
    // O(1): the plan has a fixed nine signals.
    bool push(const SignalPlan& plan) {
        if (isFull()) return false;
        plans[++topIndex] = plan;
        return true;
    }
    // O(1): an empty pop returns savedCycle == -1, with no underflow.
    SignalPlan pop() {
        return isEmpty() ? SignalPlan{} : plans[topIndex--];
    }
    SignalPlan peek() const { return isEmpty() ? SignalPlan{} : plans[topIndex]; }
};

struct Transfer {
    Vehicle vehicle;
    int targetIndex, targetLane;
};

class TrafficEngine {
public:
    CityGrid grid;
    Telemetry telemetry;
    NetworkRecords records;
    SignalPlanStack plans;
    EmergencyRequest emergencies[2];
    int cycle = 0, nextVehicleId = 1, admitted = 0, rejected = 0, cleared = 0;
    int emergencyCount = 0, gridlockEvents = 0, detourChoice = 0;
    int serviceSlots = 0, totalCrossings = 0, greenCrossings = 0, excessiveChanges = 0;
    int attemptedWeight = 0, clearedWeight = 0;
    long long totalWaiting = 0;
    double congestionSum = 0, peakCongestion = 0;
    bool roadBlocked = false, reroutedThisCycle = false;
    bool verbose = true;
    int previousHotspot = 0, feedbackIntersection = -1;
    int pendingRecommendationIntersection = -1, pendingManualIntersection = -1;

    explicit TrafficEngine(bool showMessages = true) : verbose(showMessages) {}

    static int weight(const Vehicle& vehicle) {
        return vehicle.type == "BUS" ? 2 : (vehicle.type == "AMBULANCE" ? 3 : 1);
    }

    EmergencyRequest* emergencyFor(int id) {
        for (int i = 0; i < emergencyCount; ++i)
            if (emergencies[i].vehicleId == id) return &emergencies[i];
        return nullptr;
    }

    bool blockedConnection(char from, char to) const {
        return roadBlocked && ((from == 'B' && to == 'E') || (from == 'E' && to == 'B'));
    }

    string alternateRoute(char source, int side) const {
        if (source == 'B') return side == 1 ? "BADE" : "BCFE";
        return side == 1 ? "EDAB" : "EFCB";
    }

    void setVehicleRoute(Vehicle& vehicle, const string& route, int position = 0) {
        vehicle.route = route;
        vehicle.routePosition = position;
        vehicle.destination = position + 1 < static_cast<int>(route.size())
            ? route[position + 1] : 'X';
    }

    void addTraffic(int index, int lane, int number) {
        for (int count = 0; count < number; ++count) {
            Vehicle vehicle;
            vehicle.id = nextVehicleId++;
            vehicle.type = (vehicle.id % 9 == 0) ? "BUS" : "CAR";
            vehicle.priority = vehicle.type == "BUS" ? 2 : 1;
            char source = grid.at(index).name;
            char destination = straightDestination(index, lane);
            string route(1, source);
            // Two thirds use local district exits; one third continue to a
            // neighboring intersection. This leaves recovery capacity while
            // still making road transfers and accident queues visible.
            if (destination != 'X' && vehicle.id % 3 == 0) route += destination;
            else destination = 'X';
            if (blockedConnection(source, destination) && detourChoice != 0)
                route = alternateRoute(source, detourChoice);
            setVehicleRoute(vehicle, route);
            attemptedWeight += weight(vehicle);
            if (laneQueue(grid.at(index), lane).enqueue(vehicle)) {
                ++admitted;
                ++telemetry.externalArrivals[index];
            }
            else ++rejected; // Capacity failures are penalized, never silently lost.
        }
    }

    // Same integer schedule, IDs and vehicle types for every fresh session.
    void addScheduledTraffic() {
        for (int index = 0; index < INTERSECTIONS; ++index) {
            int lane = (cycle / 3 + index) % 4;
            addTraffic(index, lane, 1);
            int opposite = lane == NORTH ? SOUTH : lane == SOUTH ? NORTH
                         : lane == EAST ? WEST : EAST;
            addTraffic(index, opposite, 1);
            if (cycle >= 12 && (cycle + index) % 3 == 0)
                addTraffic(index, (lane + 1) % 4, 1);
        }
        if (cycle == 3 || cycle == 6) {
            int index = cycle == 3 ? 1 : 3;
            addTraffic(index, EAST, 3);
            if (cycle == 6) addTraffic(5, WEST, 3);
        }
        // Repeated commuter demand makes the accident an actionable problem.
        if (cycle >= 7 && cycle <= 11) {
            addTraffic(1, NORTH, 2); // B -> E
            addTraffic(4, SOUTH, 2); // E -> B
        }
    }

    void announce(const Incident& incident, const string& location,
                  const string& impact, const string& suggestion) {
        records.incidentCategories.insert(incident.type);
        records.log(cycle, incident.type, incident.description);
        if (!verbose) return;
        cout << "\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\nTRAFFIC INCIDENT\n"
             << "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n" << incident.type
             << "\nLocation: " << location << '\n' << incident.description
             << "\nExpected impact: " << impact << "\nSuggested: " << suggestion << '\n';
    }

    void spawnEmergency(char source, int lane, const string& route) {
        if (emergencyCount >= 2) return;
        Vehicle vehicle;
        vehicle.id = nextVehicleId++;
        vehicle.type = "AMBULANCE";
        vehicle.priority = 3;
        setVehicleRoute(vehicle, route);
        EmergencyRequest& request = emergencies[emergencyCount];
        request.vehicleId = vehicle.id;
        request.enteredCycle = cycle;
        request.location = source;
        request.lane = lane;
        request.route = route;
        request.label = "AMB-0" + to_string(emergencyCount + 1);
        ++emergencyCount;
        attemptedWeight += weight(vehicle);
        if (laneQueue(grid.at(source - 'A'), lane).enqueue(vehicle)) {
            ++admitted;
            ++telemetry.externalArrivals[source - 'A'];
        }
        else ++rejected;
        records.incidentCategories.insert("EMERGENCY");
        records.log(cycle, "EMERGENCY", request.label + " entered at " + string(1, source));
        if (verbose) {
            cout << "\nEMERGENCY VEHICLE DETECTED\nVehicle: " << request.label
                 << "\nCurrent location: Intersection " << source
                 << "\nTarget: Hospital access near C\nRoute: ";
            printRoute(route);
            cout << "\nEmergency waiting: 0 cycles\n"
                 << "Use 3. PRIORITIZE EMERGENCY to form a green corridor.\n";
        }
    }

    static void printRoute(const string& route) {
        for (size_t i = 0; i < route.size(); ++i) {
            if (i) cout << " -> ";
            cout << route[i];
        }
    }

    void triggerScheduledIncident() {
        if (cycle == 4) {
            addTraffic(1, EAST, 4);
            addTraffic(4, WEST, 5);
            announce({4, "RUSH HOUR", 'B', "Traffic surge at B/E"}, "B and E",
                     "Longer queues around the city center.", "Give the busiest lanes a green signal.");
        } else if (cycle == 7) {
            roadBlocked = true;
            announce({7, "ROAD ACCIDENT", 'B', "ROAD B-E BLOCKED; capacity NORMAL -> BLOCKED"},
                     "B <-> E", "Traffic builds up at B and E; road reopens at cycle 12.",
                     "Inspect B/E or choose 4. REROUTE TRAFFIC.");
        } else if (cycle == 10) {
            // B-E is still blocked: the equally short D-E-F-C corridor is safe.
            spawnEmergency('D', WEST, roadBlocked ? "DEFC" : "DEBC");
        } else if (cycle == 12) {
            roadBlocked = false;
            detourChoice = 0;
            announce({12, "ROAD REOPENED", 'B', "Road B-E is open again; detours ended"},
                     "B <-> E", "Held traffic can now cross.", "Clear the remaining B/E queues.");
        } else if (cycle == 13) {
            addTraffic(6, EAST, 7);
            addTraffic(7, WEST, 7);
            announce({13, "STADIUM RELEASE", 'G', "Large traffic surge at G/H"}, "G and H",
                     "Heavy east/west traffic in the south.", "Favor EW at G/H when queues rise.");
        } else if (cycle == 16) {
            grid.at(4).signalOperational = false;
            announce({16, "SIGNAL FAILURE", 'E', "Intersection E signal is OFF"}, "E",
                     "E cannot discharge vehicles during cycles 16-18.",
                     "Manage neighboring queues; automatic repair is due at cycle 19.");
        } else if (cycle == 18) {
            spawnEmergency('F', NORTH, "FC");
        } else if (cycle == 19) {
            grid.at(4).signalOperational = true;
            announce({19, "SIGNAL REPAIRED", 'E', "Intersection E signal is operational again"}, "E",
                     "Traffic can move through E.", "Clear its longest queue.");
        }
    }

    bool changeSignal(int index, const string& signal, const string& reason = "SIGNAL") {
        if (index < 0 || index >= INTERSECTIONS || (signal != NS_GREEN && signal != EW_GREEN)) return false;
        Intersection& point = grid.at(index);
        if (point.signalState == signal) return true;
        string previous = point.signalState == NS_GREEN ? "NS" : "EW";
        point.signalState = signal;
        ++telemetry.signalChanges[index];
        if (++telemetry.changesThisCycle[index] > 1) ++excessiveChanges;
        records.log(cycle, reason, string(1, point.name) + " changed " + previous
                    + " -> " + (signal == NS_GREEN ? "NS" : "EW"));
        return true;
    }

    void applyGreenCorridors() {
        for (int e = 0; e < emergencyCount; ++e) {
            EmergencyRequest& request = emergencies[e];
            if (request.cleared || request.priorityUntil < cycle) continue;
            // The final C is hospital access: arrival there completes the
            // request, rather than requiring a further city crossing.
            for (int pos = request.routePosition; pos + 1 < static_cast<int>(request.route.size()); ++pos) {
                int lane = pos == request.routePosition ? request.lane
                    : incomingLane(request.route[pos - 1], request.route[pos]);
                changeSignal(request.route[pos] - 'A', northSouth(lane) ? NS_GREEN : EW_GREEN, "CORRIDOR");
            }
        }
    }

    bool prioritizeEmergency() {
        bool found = false;
        for (int i = 0; i < emergencyCount; ++i) {
            EmergencyRequest& request = emergencies[i];
            if (request.cleared) continue;
            request.priorityUntil = cycle + 4;
            records.log(cycle, "PRIORITY", request.label + " corridor enabled through cycle "
                        + to_string(min(TOTAL_CYCLES, request.priorityUntil)));
            found = true;
            if (verbose) {
                cout << request.label << ": ";
                printRoute(request.route.substr(request.routePosition));
                cout << "\nGreen corridor active for the next 4 cycles.\n"
                     << "Vehicles ahead still cross first; priority preserves lane order.\n";
            }
        }
        if (found) applyGreenCorridors();
        else if (verbose) cout << "No active emergency vehicle needs priority.\n";
        return found;
    }

    void recordCrossing(int index) {
        ++grid.at(index).vehiclesPassed;
        ++telemetry.vehiclesCleared[index];
        ++totalCrossings;
    }

    // O(I + V): examine intersections, serve at most two vehicles per green
    // lane, then update each waiting vehicle. Staged transfers ensure that a
    // vehicle crosses at most one intersection per cycle, regardless of order.
    void moveVehicles() {
        vector<Transfer> transfers;
        int reservations[INTERSECTIONS][4] = {};
        for (int i = 0; i < emergencyCount; ++i) emergencies[i].movedThisCycle = false;
        for (int index = 0; index < INTERSECTIONS; ++index) {
            Intersection& point = grid.at(index);
            if (!point.signalOperational) continue;
            serviceSlots += 2 * GREEN_LIMIT;
            for (int lane = 0; lane < 4; ++lane) {
                bool green = northSouth(lane) ? point.signalState == NS_GREEN : point.signalState == EW_GREEN;
                if (!green) continue;
                VehicleQueue& queue = laneQueue(point, lane);
                for (int served = 0; served < GREEN_LIMIT && !queue.isEmpty(); ++served) {
                    Vehicle vehicle = queue.peek();
                    EmergencyRequest* emergency = emergencyFor(vehicle.id);
                    bool hospitalArrival = emergency && vehicle.destination == 'C'
                        && vehicle.routePosition + 2 == static_cast<int>(vehicle.route.size());
                    int target = vehicle.destination == 'X' ? -1 : vehicle.destination - 'A';
                    int targetLane = -1;
                    if (target >= 0) {
                        if (blockedConnection(point.name, vehicle.destination)) break;
                        if (!hospitalArrival) {
                            targetLane = incomingLane(point.name, vehicle.destination);
                            if (laneQueue(grid.at(target), targetLane).size()
                                + reservations[target][targetLane] >= LANE_CAPACITY) break;
                        }
                    }
                    vehicle = queue.dequeue();
                    recordCrossing(index);
                    ++greenCrossings;
                    ++telemetry.vehiclesPassedSignal[index];
                    if (emergency) emergency->movedThisCycle = true;
                    if (target < 0 || hospitalArrival) {
                        ++cleared;
                        ++telemetry.networkExitsFromIntersection[index];
                        clearedWeight += weight(vehicle);
                        if (emergency) {
                            emergency->cleared = true;
                            emergency->clearedCycle = cycle;
                            emergency->location = 'C';
                            emergency->routePosition = static_cast<int>(emergency->route.size()) - 1;
                            records.processedEmergencies.insert(vehicle.id);
                            records.log(cycle, "EMERGENCY CLEARED", emergency->label + " reached hospital C");
                            if (verbose) cout << "\n" << emergency->label << " CLEARED - hospital access reached.\n";
                        }
                    } else {
                        ++vehicle.routePosition;
                        vehicle.destination = vehicle.routePosition + 1 < static_cast<int>(vehicle.route.size())
                            ? vehicle.route[vehicle.routePosition + 1] : 'X';
                        ++reservations[target][targetLane];
                        transfers.push_back({vehicle, target, targetLane});
                    }
                }
            }
        }
        for (const Transfer& transfer : transfers) {
            bool stored = laneQueue(grid.at(transfer.targetIndex), transfer.targetLane).enqueue(transfer.vehicle);
            assert(stored); // Reserved capacity guarantees this enqueue.
            if (stored) ++telemetry.internalArrivals[transfer.targetIndex];
            EmergencyRequest* emergency = emergencyFor(transfer.vehicle.id);
            if (emergency) {
                emergency->location = grid.at(transfer.targetIndex).name;
                emergency->lane = transfer.targetLane;
                emergency->routePosition = transfer.vehicle.routePosition;
            }
        }
        for (int i = 0; i < emergencyCount; ++i) {
            EmergencyRequest& request = emergencies[i];
            if (!request.cleared && !request.movedThisCycle) {
                ++request.blockedCycles;
                ++telemetry.emergencyDelays[request.location - 'A'];
            }
        }
    }

    void updateTelemetry(bool countCycle) {
        double networkCongestion = 0;
        for (int index = 0; index < INTERSECTIONS; ++index) {
            Intersection& point = grid.at(index);
            if (countCycle) {
                for (int lane = 0; lane < 4; ++lane) {
                    VehicleQueue& queue = laneQueue(point, lane);
                    for (int v = 0; v < queue.size(); ++v) {
                        queue.at(v).waitingTime += CYCLE_SECONDS;
                        point.totalWaitingTime += CYCLE_SECONDS;
                        totalWaiting += CYCLE_SECONDS;
                    }
                }
                if (queueTotal(point) >= 15) ++telemetry.gridlockStreak[index];
                else telemetry.gridlockStreak[index] = 0;
                if (telemetry.gridlockStreak[index] == 3) {
                    ++gridlockEvents;
                    records.log(cycle, "GRIDLOCK", string(1, point.name) + " held 15+ vehicles for 3 cycles");
                    if (verbose) cout << "\nGRIDLOCK EVENT RECORDED at " << point.name
                                      << ". Clear its queues to recover.\n";
                }
            }
            point.congestionLevel = min(100, queueTotal(point) * 100 / 15);
            telemetry.congestionLevels[index] = point.congestionLevel;
            telemetry.waitingTotals[index] = point.totalWaitingTime;
            telemetry.vehiclesCleared[index] = point.vehiclesPassed;
            telemetry.queueAtCycleEnd[index] = queueTotal(point);
            networkCongestion += point.congestionLevel;
        }
        networkCongestion /= INTERSECTIONS;
        peakCongestion = max(peakCongestion, networkCongestion);
        if (countCycle) congestionSum += networkCongestion;
    }

    void resetCycleTraffic() {
        for (int index = 0; index < INTERSECTIONS; ++index) {
            telemetry.queueAtCycleStart[index] = queueTotal(grid.at(index));
            telemetry.externalArrivals[index] = 0;
            telemetry.internalArrivals[index] = 0;
            telemetry.vehiclesPassedSignal[index] = 0;
            telemetry.networkExitsFromIntersection[index] = 0;
            telemetry.queueAtCycleEnd[index] = telemetry.queueAtCycleStart[index];
            telemetry.divertedOut[index] = 0;
        }
    }

    bool advanceCycle() {
        if (cycle >= TOTAL_CYCLES) return false;
        previousHotspot = dashboardMetrics().hotspot;
        // A manual signal change is useful context when no recommendation
        // was applied. Merely viewing advice never changes report selection.
        feedbackIntersection = pendingRecommendationIntersection >= 0
            ? pendingRecommendationIntersection : pendingManualIntersection;
        pendingRecommendationIntersection = pendingManualIntersection = -1;
        resetCycleTraffic();
        ++cycle;
        reroutedThisCycle = false;
        for (int& count : telemetry.changesThisCycle) count = 0;
        addScheduledTraffic();
        triggerScheduledIncident();
        applyGreenCorridors();
        moveVehicles();
        updateTelemetry(true);
        return true;
    }

    bool savePlan() {
        SignalPlan plan;
        plan.savedCycle = cycle;
        plan.detourChoice = detourChoice;
        for (int i = 0; i < INTERSECTIONS; ++i) plan.signals[i] = grid.at(i).signalState;
        if (!plans.push(plan)) {
            if (verbose) cout << "Plan history is full (20). Restore a plan to free a slot.\n";
            return false;
        }
        records.log(cycle, "SAVE", "Signal plan saved; " + to_string(plans.size()) + " plans stored");
        if (verbose) cout << "SIGNAL PLAN SAVED\nCycle " << cycle << "\nSaved plans: " << plans.size() << '\n';
        return true;
    }

    bool restorePlan(bool ask = true) {
        if (plans.isEmpty()) {
            if (verbose) cout << "No saved signal plan. Save one with option 5.\n";
            return false;
        }
        if (ask) {
            cout << "LATEST SAVED PLAN: Cycle " << plans.peek().savedCycle << '\n';
            if (!confirm("Restore")) return false;
        }
        SignalPlan plan = plans.pop();
        for (int i = 0; i < INTERSECTIONS; ++i) changeSignal(i, plan.signals[i], "RESTORE");
        detourChoice = roadBlocked ? plan.detourChoice : 0;
        records.log(cycle, "RESTORE", "Plan from cycle " + to_string(plan.savedCycle) + " restored");
        if (verbose) cout << "Signals and detour setting restored. Traffic continues from this cycle.\n";
        return true;
    }

    // Divert at most three front vehicles per blocked approach. Each transfer
    // preserves the vehicle ID and accumulated waiting time. The remaining
    // alternate route is driven by normal green signals on future cycles.
    int rerouteTraffic(int side) {
        if (!roadBlocked) {
            if (verbose) cout << "Road B-E is open. No accident detour is needed.\n";
            return 0;
        }
        if (side != 1 && side != 2) return 0;
        detourChoice = side;
        if (reroutedThisCycle) {
            if (verbose) cout << "Detour updated. Next diversion is available next cycle.\n";
            return 0;
        }
        reroutedThisCycle = true;
        int moved = 0;
        const int sources[2] = {1, 4};
        const int lanes[2] = {NORTH, SOUTH};
        for (int s = 0; s < 2; ++s) {
            int source = sources[s];
            VehicleQueue& queue = laneQueue(grid.at(source), lanes[s]);
            string route = alternateRoute(grid.at(source).name, side);
            int target = route[1] - 'A';
            int targetLane = incomingLane(route[0], route[1]);
            for (int n = 0; n < 3 && !queue.isEmpty(); ++n) {
                Vehicle vehicle = queue.peek();
                char blockedTarget = source == 1 ? 'E' : 'B';
                if (vehicle.type == "AMBULANCE" || vehicle.destination != blockedTarget
                    || laneQueue(grid.at(target), targetLane).isFull()) break;
                vehicle = queue.dequeue();
                setVehicleRoute(vehicle, route, 1);
                bool stored = laneQueue(grid.at(target), targetLane).enqueue(vehicle);
                assert(stored);
                if (stored) {
                    ++telemetry.divertedOut[source];
                    ++telemetry.internalArrivals[target];
                }
                recordCrossing(source);
                ++moved;
            }
        }
        records.log(cycle, "REROUTE", to_string(moved) + " vehicles diverted via "
                    + (side == 1 ? "A/D" : "C/F"));
        updateTelemetry(false);
        if (verbose) cout << moved << " vehicles diverted via " << (side == 1 ? "A/D" : "C/F")
                          << ". New B/E traffic uses this detour until reopening.\n"
                          << "Alternate intersections now carry more traffic.\n";
        return moved;
    }

    DashboardMetrics dashboardMetrics() const {
        DashboardMetrics metrics;
        metrics.cycle = cycle;
        metrics.networkExits = cleared; // Only complete exits / hospital arrivals.
        metrics.flow = attemptedWeight ? 100.0 * clearedWeight / attemptedWeight : 100;
        metrics.wait = admitted ? static_cast<double>(totalWaiting) / admitted : 0;
        metrics.roadBlocked = roadBlocked;
        int highest = -1;
        vector<string> active;
        for (int i = 0; i < INTERSECTIONS; ++i) {
            metrics.congestion += telemetry.congestionLevels[i];
            if (queueTotal(grid.at(i)) > highest) {
                highest = queueTotal(grid.at(i));
                metrics.hotspot = i;
            }
        }
        metrics.congestion /= INTERSECTIONS;
        for (int e = 0; e < emergencyCount; ++e) {
            const EmergencyRequest& request = emergencies[e];
            if (request.cleared) continue;
            active.push_back(request.label + " at " + string(1, request.location)
                + " / " + to_string(request.blockedCycles) + " blocked cycles"
                + (request.priorityUntil > cycle ? " / PRIORITY ON" : " / needs priority"));
        }
        if (!active.empty()) {
            metrics.emergencyStatus = active[0];
            for (size_t i = 1; i < active.size(); ++i) metrics.emergencyStatus += "; " + active[i];
        }
        return metrics;
    }

    void inspect(int index) const {
        if (index < 0 || index >= INTERSECTIONS) return;
        const Intersection& point = grid.at(index);
        cout << "\nINTERSECTION " << point.name << '\n'
             << "North/South queue : " << point.north.size() + point.south.size() << '\n'
             << "East/West queue   : " << point.east.size() + point.west.size() << '\n'
             << "Current signal    : " << (point.signalState == NS_GREEN ? "NS GREEN" : "EW GREEN")
             << (point.signalOperational ? "" : " (OFF)") << '\n'
             << "Congestion        : " << congestionLabel(queueTotal(point)) << '\n';
        for (int lane = 0; lane < 4; ++lane) {
            const VehicleQueue& queue = laneQueue(point, lane);
            cout << setw(5) << laneName(lane) << ": " << queue.size();
            if (!queue.isEmpty()) {
                Vehicle front = queue.peek();
                cout << " | first: #" << front.id << ' ' << front.type << " | wait "
                     << front.waitingTime << " sec | next: "
                     << (front.destination == 'X' ? "network exit" : string(1, front.destination));
            }
            cout << '\n';
        }
        if (roadBlocked && (index == 1 || index == 4))
            cout << "Road B-E is blocked. Option 4 offers alternate roads.\n";
        if (cycle > 0) {
            cout << "\nTHIS CYCLE TRAFFIC RESULT";
            displayIntersectionTrafficResult(grid, telemetry, index);
        }
    }

    void changeSignalMenu() {
        int index = selectIntersection();
        if (index < 0) return;
        inspect(index);
        if (!grid.at(index).signalOperational) {
            cout << "Signal is awaiting repair at cycle 19; this changes its stored plan.\n";
        }
        string signal = grid.at(index).signalState == NS_GREEN ? EW_GREEN : NS_GREEN;
        if (confirm("Change to " + string(signal == NS_GREEN ? "NS GREEN" : "EW GREEN") + "?")) {
            changeSignal(index, signal);
            pendingManualIntersection = index;
            cout << "Intersection " << grid.at(index).name << " signal changed.\n";
        }
    }

    void rerouteMenu() {
        if (!roadBlocked) { rerouteTraffic(1); return; }
        cout << "\nROAD B-E BLOCKED\nChoose alternate roads:\n"
             << "1. B -> A -> D -> E (reverse: E -> D -> A -> B)\n"
             << "2. B -> C -> F -> E (reverse: E -> F -> C -> B)\n"
             << "0. Back\n";
        int side = readMenu(0, 2);
        if (side > 0) rerouteTraffic(side);
    }

    void showHistory() const {
        cout << "\nRESPONSE / EVENT LOG\n";
        if (records.history.empty()) cout << "No events recorded yet.\n";
        for (const string& entry : records.history) cout << entry << '\n';
    }

    PerformanceReport report() const; // Contribution 5 below.
    void networkDetails() const;
    void moreDetails() const;

    // Recommendation generation is read-only. Applying one delegates to the
    // same methods as the manual menus, preserving the engine and scoring.
    int estimateSignalService(int index, const string& signal) const;
    int estimateDiversion(int side) const;
    bool corridorProtects(int index) const;
    int buildRecommendations(TrafficRecommendation output[]) const;
    void showRecommendation(const TrafficRecommendation& recommendation) const;
    bool applyRecommendation(const TrafficRecommendation& recommendation);
    bool recommendationMenu(); // true means the operator chose NEXT CYCLE.
    int selectTrafficResultIntersections(int output[]) const;
    void showLastCycleResult() const;

    bool executeCommand(const string& input) {
        ParsedCommand command = parseCommand(input);
        if (!command.valid) return false;
        int index = records.indexOf(command.intersection);
        if (command.action == "SIGNAL") {
            changeSignal(index, command.value == "NS" ? NS_GREEN : EW_GREEN);
            pendingManualIntersection = index;
            if (verbose) cout << "Signal setting applied to " << command.intersection << ".\n";
        } else if (command.action == "INSPECT") inspect(index);
        else if (command.action == "EMERGENCY") prioritizeEmergency();
        else if (command.action == "SAVE") savePlan();
        else if (command.action == "RESTORE") restorePlan();
        return true;
    }

    // Simple demonstration strategy: favor the busiest approach, divert
    // blocked traffic, and activate emergency corridors. No graph algorithms.
    void responsiveStrategy() {
        if (roadBlocked) rerouteTraffic(cycle % 2 == 0 ? 1 : 2);
        for (int index = 0; index < INTERSECTIONS; ++index) {
            Intersection& point = grid.at(index);
            int ns = point.north.size() + point.south.size();
            int ew = point.east.size() + point.west.size();
            if (roadBlocked) {
                if (index == 1) ns -= point.north.size();
                if (index == 4) ns -= point.south.size();
            }
            if (ns > ew) changeSignal(index, NS_GREEN);
            if (ew > ns) changeSignal(index, EW_GREEN);
        }
        bool needsPriority = false;
        for (int e = 0; e < emergencyCount; ++e)
            if (!emergencies[e].cleared && emergencies[e].priorityUntil <= cycle + 1) needsPriority = true;
        if (needsPriority) prioritizeEmergency();
        else applyGreenCorridors();
    }
};

// ============================================================
// CONTRIBUTION 2: COMPACT LAST-CYCLE FEEDBACK
// Show the previous hotspot and the last recommended / changed intersection,
// deduplicated, plus the largest significant change (four or more vehicles).
// Usually one or two results; at most three, never the entire city by default.
// ============================================================
int TrafficEngine::selectTrafficResultIntersections(int output[]) const {
    int count = 0;
    output[count++] = previousHotspot;
    if (feedbackIntersection >= 0 && feedbackIntersection != previousHotspot)
        output[count++] = feedbackIntersection;
    int significant = -1, largestChange = SIGNIFICANT_QUEUE_CHANGE - 1;
    for (int index = 0; index < INTERSECTIONS; ++index) {
        bool selected = false;
        for (int n = 0; n < count; ++n) if (output[n] == index) selected = true;
        int change = abs(telemetry.queueAtCycleEnd[index] - telemetry.queueAtCycleStart[index]);
        if (!selected && change > largestChange) {
            largestChange = change;
            significant = index;
        }
    }
    if (significant >= 0) output[count++] = significant;
    return count;
}

void TrafficEngine::showLastCycleResult() const {
    cout << '\n' << BORDER << "\nLAST CYCLE TRAFFIC RESULT // CYCLE " << cycle
         << '\n' << BORDER << '\n';
    int selected[MAX_TRAFFIC_RESULTS];
    int count = selectTrafficResultIntersections(selected);
    for (int n = 0; n < count; ++n)
        displayIntersectionTrafficResult(grid, telemetry, selected[n]);
    cout << "\nInspect an intersection (option 7) to see its full movement result.\n";
}

// ============================================================
// CONTRIBUTION 1 + 2: RULE-BASED TRAFFIC RECOMMENDATIONS & UI
// Rules: unprioritized emergency first, available accident detours next,
// then useful signal changes ordered by queue imbalance. Otherwise advance.
// ============================================================
int TrafficEngine::estimateSignalService(int index, const string& signal) const {
    if (!grid.at(index).signalOperational) return 0;
    int served = 0;
    int reservations[INTERSECTIONS][4] = {};
    for (int lane = 0; lane < 4; ++lane) {
        if ((northSouth(lane) ? NS_GREEN : EW_GREEN) != signal) continue;
        const VehicleQueue& queue = laneQueue(grid.at(index), lane);
        for (int n = 0; n < min(GREEN_LIMIT, queue.size()); ++n) {
            const Vehicle& vehicle = queue.at(n);
            if (blockedConnection(grid.at(index).name, vehicle.destination)) break;
            bool hospitalArrival = false;
            for (int e = 0; e < emergencyCount; ++e)
                if (emergencies[e].vehicleId == vehicle.id && vehicle.destination == 'C'
                    && vehicle.routePosition + 2 == static_cast<int>(vehicle.route.size()))
                    hospitalArrival = true;
            if (vehicle.destination != 'X' && !hospitalArrival) {
                int target = vehicle.destination - 'A';
                int targetLane = incomingLane(grid.at(index).name, vehicle.destination);
                if (laneQueue(grid.at(target), targetLane).size()
                    + reservations[target][targetLane] >= LANE_CAPACITY) break;
                ++reservations[target][targetLane];
            }
            ++served;
        }
    }
    return served;
}

int TrafficEngine::estimateDiversion(int side) const {
    if (!roadBlocked || reroutedThisCycle) return 0;
    int moved = 0;
    const int sources[2] = {1, 4}, lanes[2] = {NORTH, SOUTH};
    for (int s = 0; s < 2; ++s) {
        string route = alternateRoute(grid.at(sources[s]).name, side);
        const VehicleQueue& queue = laneQueue(grid.at(sources[s]), lanes[s]);
        int space = LANE_CAPACITY - laneQueue(grid.at(route[1] - 'A'), incomingLane(route[0], route[1])).size();
        for (int n = 0; n < min(3, min(space, queue.size())); ++n) {
            const Vehicle& vehicle = queue.at(n);
            if (vehicle.type == "AMBULANCE" || vehicle.destination != (s == 0 ? 'E' : 'B')) break;
            ++moved;
        }
    }
    return moved;
}

bool TrafficEngine::corridorProtects(int index) const {
    for (int e = 0; e < emergencyCount; ++e) {
        const EmergencyRequest& request = emergencies[e];
        if (request.cleared || request.priorityUntil <= cycle) continue;
        for (int pos = request.routePosition; pos + 1 < static_cast<int>(request.route.size()); ++pos)
            if (request.route[pos] == grid.at(index).name) return true;
    }
    return false;
}

// Simple conditions, loops and a fixed array. Ties use intersection order
// so identical states always produce identical advice. Inspection never
// mutates queues, signals, time, statistics, the plan stack or event history.
int TrafficEngine::buildRecommendations(TrafficRecommendation output[]) const {
    int count = 0;
    if (cycle < TOTAL_CYCLES) {
        int urgent = -1;
        for (int e = 0; e < emergencyCount; ++e) {
            const EmergencyRequest& request = emergencies[e];
            if (!request.cleared && request.priorityUntil <= cycle
                && (urgent == -1 || request.blockedCycles > emergencies[urgent].blockedCycles)) urgent = e;
        }
        if (urgent >= 0) {
            TrafficRecommendation recommendation;
            recommendation.action = RECOMMEND_EMERGENCY;
            recommendation.emergency = urgent;
            output[count++] = recommendation;
            return count; // Ordinary alternatives must not distract from an emergency.
        }
        if (roadBlocked && !reroutedThisCycle) {
            int preferred = queueTotal(grid.at(0)) + queueTotal(grid.at(3))
                         <= queueTotal(grid.at(2)) + queueTotal(grid.at(5)) ? 1 : 2;
            for (int choice = 0; choice < 2; ++choice) {
                int side = choice == 0 ? preferred : 3 - preferred;
                int ready = estimateDiversion(side);
                string fromB = alternateRoute('B', side), fromE = alternateRoute('E', side);
                bool space = !laneQueue(grid.at(fromB[1] - 'A'), incomingLane('B', fromB[1])).isFull()
                          && !laneQueue(grid.at(fromE[1] - 'A'), incomingLane('E', fromE[1])).isFull();
                if (ready == 0 && (detourChoice != 0 || !space)) continue;
                TrafficRecommendation recommendation;
                recommendation.action = RECOMMEND_DETOUR;
                recommendation.detour = side;
                recommendation.expectedVehicles = ready;
                output[count++] = recommendation;
            }
        }
        int signalsBegin = count;
        for (int index = 0; index < INTERSECTIONS; ++index) {
            const Intersection& point = grid.at(index);
            if (!point.signalOperational || corridorProtects(index)) continue;
            int ns = point.north.size() + point.south.size();
            int ew = point.east.size() + point.west.size();
            int green = point.signalState == NS_GREEN ? ns : ew;
            int red = point.signalState == NS_GREEN ? ew : ns;
            string desired = point.signalState == NS_GREEN ? EW_GREEN : NS_GREEN;
            int expected = estimateSignalService(index, desired);
            if (expected == 0 || (red <= green && estimateSignalService(index, point.signalState) > 0)) continue;
            TrafficRecommendation recommendation;
            recommendation.action = RECOMMEND_SIGNAL;
            recommendation.intersection = index;
            recommendation.signal = desired;
            recommendation.expectedVehicles = expected;
            recommendation.queueDifference = red - green;
            int position = count++;
            // Insertion into the small recommendation array; larger queue
            // imbalance comes first. Detours keep their higher priority.
            while (position > signalsBegin && output[position - 1].queueDifference < recommendation.queueDifference) {
                output[position] = output[position - 1];
                --position;
            }
            output[position] = recommendation;
        }
    }
    output[count++] = TrafficRecommendation{}; // Keep plan / final assessment.
    return count;
}

void TrafficEngine::showRecommendation(const TrafficRecommendation& recommendation) const {
    cout << '\n' << BORDER << "\n          TRAFFIC RECOMMENDATION\n" << BORDER << '\n';
    if (recommendation.action == RECOMMEND_EMERGENCY) {
        const EmergencyRequest& request = emergencies[recommendation.emergency];
        cout << "\nURGENT: " << request.label << " is waiting at Intersection " << request.location
             << ".\n\nCURRENT ISSUE:\nEmergency priority is not enabled for the next cycle.\n\nRoute: ";
        printRoute(request.route.substr(request.routePosition));
        cout << "\nBlocked Cycles: " << request.blockedCycles
             << "\n\nRECOMMENDED ACTION:\nEnable Emergency Priority\n\nWHY:\n"
             << "The ambulance needs a green corridor to reach hospital access near C.\n"
             << "Every blocked cycle reduces its emergency response score.\n\nEXPECTED EFFECT:\n"
             << "Signals along its route will favor the ambulance's approach\n"
             << "for the next 4 cycles.\n\nNOTE:\n"
             << "Vehicles ahead still cross first; blocked roads or failed signals may delay travel.\n";
    } else if (recommendation.action == RECOMMEND_DETOUR) {
        string side = recommendation.detour == 1 ? "A/D" : "C/F";
        cout << "\nCURRENT ISSUE:\nRoad B-E is blocked. Traffic cannot cross directly between B and E.\n"
             << "B north queue: " << grid.at(1).north.size()
             << " | E south queue: " << grid.at(4).south.size()
             << "\n\nRECOMMENDED ACTION:\nReroute traffic via " << side << "\n";
        printRoute(alternateRoute('B', recommendation.detour));
        cout << " (reverse: "; printRoute(alternateRoute('E', recommendation.detour)); cout << ")\n";
        cout << "\nWHY:\nThese predefined roads avoid the accident.\n"
             << "Available entry space permits the estimated diversion below.\n\nEXPECTED EFFECT:\n"
             << "Up to " << recommendation.expectedVehicles << " currently waiting vehicles can be diverted now.\n"
             << "New B/E arrivals will use this detour until the road reopens.\n\nNOTE:\n"
             << "Traffic is moved to alternate intersections; it still needs green signals.\n"
             << "Vehicles not at the front cannot overtake. Monitor " << side << " queues.\n";
    } else if (recommendation.action == RECOMMEND_SIGNAL) {
        const Intersection& point = grid.at(recommendation.intersection);
        string axis = recommendation.signal == NS_GREEN ? "North/South" : "East/West";
        cout << "\nCURRENT ISSUE:\nIntersection " << point.name << " has waiting " << axis
             << " traffic on red.\n\n" << point.name << " Queue:\nNorth/South : "
             << point.north.size() + point.south.size() << "\nEast/West   : "
             << point.east.size() + point.west.size() << "\n\nCurrent Signal:\n"
             << (point.signalState == NS_GREEN ? "NS GREEN" : "EW GREEN")
             << "\n\nRECOMMENDED ACTION:\nSwitch " << point.name << " to "
             << (recommendation.signal == NS_GREEN ? "NS GREEN" : "EW GREEN") << "\n\nWHY:\n";
        if (recommendation.queueDifference > 0)
            cout << axis << " has " << recommendation.queueDifference << " more waiting vehicles\nthan the current green direction.\n";
        else cout << "The current green lanes cannot move traffic; the other direction can.\n";
        cout << "\nEXPECTED EFFECT:\nUp to " << recommendation.expectedVehicles << " currently waiting " << axis
             << " vehicles\nmay be served at " << point.name << " during the next cycle.\n\nNOTE:\n"
             << "New traffic may still arrive, so the total queue may not fall by exactly\n"
             << recommendation.expectedVehicles << ". Each green lane serves at most " << GREEN_LIMIT
             << " vehicles (up to " << 2 * GREEN_LIMIT << " per intersection).\n"
             << "Road or downstream queue conditions may also limit movement.\n";
    } else if (cycle >= TOTAL_CYCLES) {
        cout << "\nCURRENT ISSUE:\nAll 20 traffic cycles are complete.\n\nRECOMMENDED ACTION:\n"
             << "Open the final performance assessment\n\nWHY:\nThere is no further cycle to control.\n\n"
             << "EXPECTED EFFECT:\nView the Network Efficiency Index for this session.\n";
    } else {
        cout << "\nCURRENT ISSUE:\nTraffic is waiting for the next simulation cycle.\n\n"
             << "RECOMMENDED ACTION:\nKeep the current signal plan and advance one cycle\n\nWHY:\n"
             << "Vehicles move when a cycle advances; the current controls remain in use.\n\nEXPECTED EFFECT:\n"
             << "The next cycle processes traffic and updates the queues.\n\nNOTE:\n"
             << "New arrivals can change which intersection needs attention.\n";
    }
    if (!grid.at(4).signalOperational && cycle < TOTAL_CYCLES)
        cout << "\nSIGNAL E: OFF until cycle 19. A signal change cannot repair it.\n";
}

bool TrafficEngine::applyRecommendation(const TrafficRecommendation& recommendation) {
    // Reject stale advice instead of changing a signal which now serves a
    // priority corridor, or repeating a diversion after its cycle allowance.
    TrafficRecommendation current[MAX_RECOMMENDATIONS];
    int count = buildRecommendations(current);
    bool available = false;
    for (int i = 0; i < count; ++i)
        if (current[i].action == recommendation.action && current[i].intersection == recommendation.intersection
            && current[i].emergency == recommendation.emergency && current[i].detour == recommendation.detour
            && current[i].signal == recommendation.signal) available = true;
    if (!available) {
        if (verbose) cout << "The state has changed. Get a fresh recommendation.\n";
        return false;
    }
    string action;
    int affected = -1;
    if (recommendation.action == RECOMMEND_EMERGENCY) {
        affected = emergencies[recommendation.emergency].location - 'A';
        if (!prioritizeEmergency()) return false;
        action = "Emergency priority enabled";
    } else if (recommendation.action == RECOMMEND_DETOUR) {
        affected = grid.at(1).north.size() >= grid.at(4).south.size() ? 1 : 4;
        rerouteTraffic(recommendation.detour);
        action = "Traffic detour applied via " + string(recommendation.detour == 1 ? "A/D" : "C/F");
    } else if (recommendation.action == RECOMMEND_SIGNAL) {
        affected = recommendation.intersection;
        if (!changeSignal(recommendation.intersection, recommendation.signal)) return false;
        action = string(1, grid.at(recommendation.intersection).name) + " switched to "
               + (recommendation.signal == NS_GREEN ? "NS GREEN" : "EW GREEN");
    } else action = cycle < TOTAL_CYCLES ? "Keep current plan and advance cycle" : "Open final assessment";
    if (affected >= 0) pendingRecommendationIntersection = affected;
    records.log(cycle, "RECOMMENDATION", action);
    if (verbose) cout << "\nRECOMMENDATION APPLIED: " << action << ".\n";
    return true;
}

bool TrafficEngine::recommendationMenu() {
    TrafficRecommendation recommendations[MAX_RECOMMENDATIONS];
    int count = buildRecommendations(recommendations), selected = 0;
    while (!inputClosed) {
        showRecommendation(recommendations[selected]);
        bool urgent = recommendations[selected].action == RECOMMEND_EMERGENCY;
        cout << "\n1. APPLY RECOMMENDATION\n";
        if (urgent) cout << "2. BACK\n";
        else cout << "2. VIEW ALTERNATIVE\n3. BACK\n";
        int choice = readMenu(1, urgent ? 2 : 3);
        if (choice == -1 || (urgent && choice == 2) || choice == 3) return false;
        if (choice == 1) {
            bool applied = applyRecommendation(recommendations[selected]);
            return applied && recommendations[selected].action == RECOMMEND_NEXT;
        }
        if (count == 1) cout << "No other useful action is available right now.\n";
        else {
            selected = (selected + 1) % count;
            cout << "\nShowing recommendation " << selected + 1 << " of " << count << ".\n";
        }
    }
    return false;
}

// ============================================================
// CONTRIBUTION 5 - 15%: ANALYTICS, COMPARISON & BIG-O INFORMATION
// ============================================================
double bounded(double value) { return max(0.0, min(100.0, value)); }

PerformanceReport TrafficEngine::report() const {
    PerformanceReport result;
    result.cyclesCompleted = cycle;
    result.vehiclesProcessed = cleared;
    result.vehiclesArrived = admitted;
    result.vehiclesRejected = rejected;
    result.averageWaiting = admitted ? static_cast<double>(totalWaiting) / admitted : 0;
    result.peakCongestion = peakCongestion;
    result.emergencyCleared = static_cast<int>(records.processedEmergencies.size());
    result.emergencyTotal = emergencyCount;
    result.gridlockEvents = gridlockEvents;
    for (int i = 0; i < INTERSECTIONS; ++i) {
        result.signalChanges += telemetry.signalChanges[i];
        result.vehiclesRemaining += queueTotal(grid.at(i));
    }
    // BUS counts as 2, CAR as 1, AMBULANCE as 3 in weighted traffic flow.
    // Rejected arrivals remain in the denominator. Only network exits count
    // as cleared: crossing several signals never counts a vehicle twice.
    result.trafficFlow = attemptedWeight ? bounded(100.0 * clearedWeight / attemptedWeight) : 100;
    // Mean accumulated wait includes vehicles still queued at the end.
    // 100 seconds of mean waiting uses the entire waiting score allowance.
    result.waitingPerformance = bounded(100.0 - result.averageWaiting);
    double response = 0;
    for (int i = 0; i < emergencyCount; ++i) {
        const EmergencyRequest& request = emergencies[i];
        // Every blocked cycle costs 12 points; uncleared requests score zero.
        if (request.cleared) response += bounded(100.0 - 12.0 * request.blockedCycles);
    }
    result.emergencyResponse = emergencyCount ? response / emergencyCount : 100;
    result.congestionControl = bounded(100.0 - (cycle ? congestionSum / cycle : 0)
                                       - 5.0 * gridlockEvents);
    // Signal efficiency rewards use of available green-lane capacity and
    // discourages repeatedly flipping the same signal in a single cycle.
    // Approved diversions are excluded from green-lane service utilization.
    result.signalEfficiency = bounded(serviceSlots ? 100.0 * greenCrossings / serviceSlots
                                      - 2.0 * excessiveChanges : 100);
    result.efficiencyIndex = bounded(0.30 * result.trafficFlow + 0.25 * result.waitingPerformance
        + 0.20 * result.emergencyResponse + 0.15 * result.congestionControl
        + 0.10 * result.signalEfficiency);
    return result;
}

void showAssessment(const PerformanceReport& result, const string& name) {
    cout << '\n' << BORDER << "\n      TRAFFIC PERFORMANCE ASSESSMENT\n"
         << BORDER << "\nOperator: " << name << '\n'
         << "Network exits               : " << result.vehiclesProcessed << '\n'
         << fixed << setprecision(1)
         << "Average waiting time        : " << result.averageWaiting << " sec\n"
         << "Peak congestion             : " << result.peakCongestion << "%\n"
         << "Emergency vehicles cleared  : " << result.emergencyCleared << " / " << result.emergencyTotal << '\n'
         << "Gridlock events             : " << result.gridlockEvents << '\n'
         << "Signal changes              : " << result.signalChanges << '\n'
         << "Vehicles still waiting      : " << result.vehiclesRemaining << '\n'
         << "Arrivals rejected (full lane): " << result.vehiclesRejected << "\n\n"
         << "Traffic flow                : " << result.trafficFlow << "%\n"
         << "Waiting performance         : " << result.waitingPerformance << "%\n"
         << "Emergency response          : " << result.emergencyResponse << "%\n"
         << "Congestion control          : " << result.congestionControl << "%\n"
         << "Signal efficiency           : " << result.signalEfficiency << "%\n"
         << string(50, '-') << "\nNETWORK EFFICIENCY INDEX\n\n                 "
         << result.efficiencyIndex << " / 100\n\n"
         << (result.cyclesCompleted == TOTAL_CYCLES ? "SIMULATION COMPLETED" : "SESSION ENDED EARLY")
         << '\n';
}

void compareReports(const PerformanceReport& a, const PerformanceReport& b) {
    cout << '\n' << BORDER << "\n      OPERATOR PERFORMANCE COMPARISON\n" << BORDER << '\n'
         << left << setw(26) << "" << right << setw(10) << "OP-A" << setw(10) << "OP-B" << '\n';
    cout << left << setw(26) << "Network exits" << right << setw(10) << a.vehiclesProcessed
         << setw(10) << b.vehiclesProcessed << '\n' << fixed << setprecision(1);
    const string labels[5] = {"Average wait (sec)", "Emergency score", "Gridlock events",
                              "Peak congestion (%)", "NETWORK EFFICIENCY"};
    const double valuesA[5] = {a.averageWaiting, a.emergencyResponse, static_cast<double>(a.gridlockEvents),
                               a.peakCongestion, a.efficiencyIndex};
    const double valuesB[5] = {b.averageWaiting, b.emergencyResponse, static_cast<double>(b.gridlockEvents),
                               b.peakCongestion, b.efficiencyIndex};
    for (int i = 0; i < 5; ++i) {
        cout << left << setw(26) << labels[i] << right;
        if (i == 2) cout << setw(10) << static_cast<int>(valuesA[i]) << setw(10) << static_cast<int>(valuesB[i]);
        else cout << setw(10) << valuesA[i] << setw(10) << valuesB[i];
        cout << '\n';
    }
    cout << "\nHIGHER NETWORK PERFORMANCE:\n";
    // Compare at the same one-decimal precision shown to the operators.
    if (round(a.efficiencyIndex * 10) == round(b.efficiencyIndex * 10)) cout << "EQUAL PERFORMANCE\n";
    else cout << (a.efficiencyIndex > b.efficiencyIndex ? "OPERATOR A\n" : "OPERATOR B\n");
}

void showComplexity() {
    cout << "\nCOMPLEXITY INFORMATION\n"
         << "Circular queue enqueue / dequeue : O(1), no element shifting\n"
         << "Signal plan stack push / pop     : O(1), fixed nine-signal plan\n"
         << "1D array access                  : O(1)\n"
         << "Grid traversal                   : O(R*C), O(N^2) for N x N\n"
         << "Intersection hash lookup         : O(1) average, O(I) worst\n"
         << "History vector append            : O(1) amortized\n"
         << "Unique emergency set insertion   : O(log E)\n"
         << "Full traffic cycle               : approximately O(I + V)\n"
         << "I = intersections; V = vehicles visited or processed.\n"
         << "Queues store 50 vehicles per lane; stack stores 20 plans.\n";
}

void TrafficEngine::networkDetails() const {
    while (!inputClosed) {
        cout << "\nNETWORK DETAILS\n1. Full intersection statistics\n2. 3x3 congestion matrix\n"
             << "3. Queue sizes\n4. Signal plan stack\n5. Complexity / scoring / optional commands\n6. Back\n";
        int choice = readMenu(1, 6);
        if (choice == -1 || choice == 6) return;
        if (choice == 1) {
            cout << "Name  Departed  Wait(sec)  Congestion  Changes  Emergency delays\n";
            for (int i = 0; i < INTERSECTIONS; ++i)
                cout << grid.at(i).name << setw(11) << telemetry.vehiclesCleared[i]
                     << setw(11) << telemetry.waitingTotals[i] << setw(11) << telemetry.congestionLevels[i]
                     << '%' << setw(9) << telemetry.signalChanges[i] << setw(12) << telemetry.emergencyDelays[i] << '\n';
        } else if (choice == 2) displayCongestionMatrix(grid);
        else if (choice == 3) {
            cout << "Name   North  South   East   West\n";
            for (int i = 0; i < INTERSECTIONS; ++i) {
                cout << grid.at(i).name << "   ";
                for (int lane = 0; lane < 4; ++lane) cout << setw(7) << laneQueue(grid.at(i), lane).size();
                cout << '\n';
            }
        } else if (choice == 4) {
            cout << "Saved plans: " << plans.size() << " / 20\n";
            if (!plans.isEmpty()) cout << "Latest plan: cycle " << plans.peek().savedCycle << " (restored first)\n";
            cout << "Restore changes signals and detour control; it preserves traffic, time and incidents.\n";
        } else {
            showComplexity();
            cout << "\nSCORING (all scores 0-100)\n"
                 << "Flow = weighted network exits / weighted attempted arrivals.\n"
                 << "Vehicle weights: CAR=1, BUS=2, AMBULANCE=3.\n"
                 << "Mean wait = accumulated vehicle-seconds / admitted vehicles.\n"
                 << "Waiting score = 100 - mean wait in seconds.\n"
                 << "Emergency score = mean(100 - 12 per blocked cycle); uncleared = 0.\n"
                 << "Congestion score = 100 - mean congestion - 5 per gridlock event.\n"
                 << "Signal score = green capacity used (%) - 2 per repeated same-cycle change.\n"
                 << "Index weights: flow 30%, wait 25%, emergency 20%, congestion 15%, signal 10%.\n"
                 << "\nOPTIONAL COMMANDS (enter at dashboard Choice >)\n"
                 << "SIGNAL:B:NS  SIGNAL:E:EW  INSPECT:D\n"
                 << "EMERGENCY:PRIORITIZE  SAVE:PLAN  RESTORE:PLAN\n";
        }
    }
}

void TrafficEngine::moreDetails() const {
    while (!inputClosed) {
        cout << "\nMORE / DETAILS\n1. NETWORK DETAILS\n2. EVENT LOG\n3. BACK\n";
        int choice = readMenu(1, 3);
        if (choice == -1 || choice == 3) return;
        if (choice == 1) networkDetails();
        else showHistory();
    }
}

// ============================================================
// CONTRIBUTION 1 - 40%: SINGLE / COMPETITIVE SESSION INTEGRATION
// ============================================================
void startup() {
    cout << BORDER << "\n                 GRIDLOCK-X\n" << BORDER
         << "\n\nSmart Traffic Control Simulation\n\nOBJECTIVE:\n"
         << "Keep traffic moving for 20 cycles.\nReduce waiting time, prevent gridlock,\n"
         << "and prioritize emergency vehicles.\n\nPress ENTER to begin...";
    string input;
    if (!getline(cin, input)) inputClosed = true;
}

PerformanceReport runSession(const string& name, bool automatic = false, bool responsive = false,
                             bool showScreens = true) {
    // A completely fresh object resets queues, arrays, signals, IDs, incidents,
    // stack, emergency requests, maps, sets, logs and every metric.
    TrafficEngine engine(showScreens);
    if (!automatic) {
        cout << "\n" << name << " - cars keep coming. Control signals and keep the city moving.\n"
             << "Changes affect the NEXT cycle. Press ENTER to start...";
        string input;
        if (!getline(cin, input)) inputClosed = true;
        if (inputClosed) return engine.report();
    }
    for (int step = 0; step < TOTAL_CYCLES && !inputClosed; ++step) {
        engine.advanceCycle();
        if (showScreens && step > 0) engine.showLastCycleResult();
        if (automatic) {
            if (showScreens) displayDashboard(engine.grid, engine.dashboardMetrics(), name);
            if (responsive && step + 1 < TOTAL_CYCLES) engine.responsiveStrategy();
            continue;
        }
        bool nextCycle = false;
        while (!nextCycle && !inputClosed) {
            displayDashboard(engine.grid, engine.dashboardMetrics(), name);
            cout << "Choice > ";
            string choice;
            if (!readInput(choice)) break;
            if (choice == "1") nextCycle = engine.recommendationMenu();
            else if (choice == "2") engine.changeSignalMenu();
            else if (choice == "3") engine.prioritizeEmergency();
            else if (choice == "4") engine.rerouteMenu();
            else if (choice == "5") engine.savePlan();
            else if (choice == "6") engine.restorePlan();
            else if (choice == "7") { int index = selectIntersection(); if (index >= 0) engine.inspect(index); }
            else if (choice == "8") engine.moreDetails();
            else if (choice == "9") nextCycle = true;
            else if (!engine.executeCommand(choice)) cout << "Choose a menu number from 1 to 9.\n";
        }
    }
    PerformanceReport result = engine.report();
    if (showScreens) showAssessment(result, name);
    return result;
}

// In-file verification keeps the delivered project to ONE source file.
// These tests are invoked explicitly, so no DSA material appears at startup.
bool runSelfTests() {
    int checks = 0, failures = 0;
    auto check = [&](bool condition, const string& label) {
        ++checks;
        if (!condition) { ++failures; cout << "FAIL: " << label << '\n'; }
    };
    VehicleQueue queue;
    check(queue.isEmpty() && queue.dequeue().id == 0 && queue.peek().id == 0, "queue underflow");
    for (int id = 1; id <= LANE_CAPACITY; ++id) {
        Vehicle vehicle; vehicle.id = id;
        check(queue.enqueue(vehicle), "queue fill");
    }
    check(queue.isFull() && !queue.enqueue(Vehicle{}), "queue overflow protection");
    for (int id = 1; id <= 25; ++id) check(queue.dequeue().id == id, "queue FIFO before wrap");
    for (int id = 51; id <= 75; ++id) {
        Vehicle vehicle; vehicle.id = id;
        check(queue.enqueue(vehicle), "queue wrapped enqueue");
    }
    for (int id = 26; id <= 75; ++id) check(queue.dequeue().id == id, "queue FIFO after wrap");
    check(queue.isEmpty(), "queue drains fully");

    SignalPlanStack stack;
    check(stack.isEmpty() && stack.pop().savedCycle == -1, "stack underflow");
    for (int i = 1; i <= PLAN_CAPACITY; ++i) {
        SignalPlan plan; plan.savedCycle = i;
        check(stack.push(plan), "stack push");
    }
    check(stack.isFull() && !stack.push(SignalPlan{}), "stack overflow protection");
    check(stack.peek().savedCycle == PLAN_CAPACITY && stack.size() == PLAN_CAPACITY, "peek preserves stack");
    for (int i = PLAN_CAPACITY; i >= 1; --i) check(stack.pop().savedCycle == i, "stack LIFO");

    check(parseCommand(" signal:b:ew ").valid, "case and whitespace normalization");
    const string malformed[] = {"", "SIGNAL", "SIGNAL:", "SIGNAL:B:", "SIGNAL:Z:NS", "SIGNAL:B:NS:X",
                                 "INSPECT:DD", "SAVE:PLANS", "EMERGENCY:", "999999999999999999999999"};
    for (const string& text : malformed) check(!parseCommand(text).valid, "malformed command rejection");

    // Each test group releases its large fixed-array city before the next
    // group, keeping verification within the normal Windows stack limit.
    {
        TrafficEngine engine(false);
        check(engine.records.indexOf('E') == 4 && engine.records.indexOf('Z') == -1, "STL coordinate lookup");
        engine.advanceCycle();
        check(engine.changeSignal(1, NS_GREEN), "signal change");
        engine.savePlan();
        int originalCycle = engine.cycle, originalAdmitted = engine.admitted;
        int savedQueue = queueTotal(engine.grid.at(1));
        engine.changeSignal(1, EW_GREEN);
        check(engine.restorePlan(false) && engine.grid.at(1).signalState == NS_GREEN, "signal restore");
        check(engine.cycle == originalCycle && engine.admitted == originalAdmitted
              && queueTotal(engine.grid.at(1)) == savedQueue, "restore preserves time and vehicles");
        check(!engine.restorePlan(false), "restore empty history");
        while (engine.cycle < 7) engine.advanceCycle();
        check(engine.roadBlocked && engine.blockedConnection('B', 'E') && engine.blockedConnection('E', 'B'), "accident closure");
        int before = 0;
        for (int i = 0; i < 9; ++i) before += queueTotal(engine.grid.at(i));
        int diverted = engine.rerouteTraffic(1);
        int after = 0;
        for (int i = 0; i < 9; ++i) after += queueTotal(engine.grid.at(i));
        check(diverted > 0 && before == after && engine.detourChoice == 1, "reroute conserves vehicles");
        check(engine.rerouteTraffic(2) == 0 && engine.detourChoice == 2, "diversion limited per cycle");
        engine.savePlan();
        while (engine.cycle < 10) engine.advanceCycle();
        check(engine.emergencyCount == 1 && engine.emergencies[0].route == "DEFC", "safe ambulance alternate route");
        check(engine.prioritizeEmergency() && engine.emergencies[0].priorityUntil == 14, "ambulance priority");
        while (engine.cycle < TOTAL_CYCLES) {
            engine.advanceCycle();
            if (engine.cycle == 12) check(!engine.roadBlocked, "road reopening");
            if (engine.cycle == 16) check(!engine.grid.at(4).signalOperational, "signal failure");
            if (engine.cycle == 19) check(engine.grid.at(4).signalOperational, "signal repair");
            if (engine.cycle < TOTAL_CYCLES) engine.responsiveStrategy();
            int remaining = 0;
            for (int i = 0; i < 9; ++i) remaining += queueTotal(engine.grid.at(i));
            check(engine.admitted == engine.cleared + remaining, "cycle vehicle conservation");
        }
        check(!engine.advanceCycle() && engine.cycle == 20, "cycle limit");
        check(engine.emergencyCount == 2, "second scheduled ambulance");
        check(engine.restorePlan(false) && !engine.roadBlocked && engine.grid.at(4).signalOperational,
              "old plan cannot rewind physical incidents");
        PerformanceReport report = engine.report();
        check(report.efficiencyIndex >= 0 && report.efficiencyIndex <= 100, "bounded efficiency index");

        // A clear corridor delivers an ambulance one hop per cycle until hospital
        // arrival; priority may not overtake vehicles in the same lane.
        TrafficEngine isolated(false);
        isolated.cycle = 10;
        Vehicle front; front.id = isolated.nextVehicleId++; front.route = "D";
        isolated.grid.at(3).west.enqueue(front);
        ++isolated.admitted; ++isolated.attemptedWeight;
        isolated.spawnEmergency('D', WEST, "DEBC");
        isolated.prioritizeEmergency();
        isolated.moveVehicles();
        check(isolated.emergencies[0].location == 'E' && isolated.cleared == 1, "priority keeps FIFO and one-hop movement");
        for (int move = 0; move < 3; ++move) {
            ++isolated.cycle;
            isolated.applyGreenCorridors();
            isolated.moveVehicles();
        }
        check(isolated.emergencies[0].cleared && isolated.records.processedEmergencies.size() == 1,
              "ambulance reaches hospital exactly once");

        TrafficEngine held(false);
        held.roadBlocked = true;
        held.grid.at(1).signalState = NS_GREEN;
        Vehicle first; first.id = 101; first.route = "BE"; first.destination = 'E';
        Vehicle second; second.id = 102; second.route = "B";
        held.grid.at(1).north.enqueue(first);
        held.grid.at(1).north.enqueue(second);
        held.moveVehicles();
        check(held.grid.at(1).north.size() == 2 && held.grid.at(1).north.peek().id == 101
              && held.cleared == 0, "accident blocks front vehicle without FIFO overtaking");

        TrafficEngine fullRoad(false);
        fullRoad.grid.at(1).signalState = NS_GREEN;
        fullRoad.grid.at(4).signalState = EW_GREEN;
        fullRoad.grid.at(1).north.enqueue(first);
        for (int i = 0; i < LANE_CAPACITY; ++i) {
            Vehicle resident; resident.id = 200 + i;
            fullRoad.grid.at(4).north.enqueue(resident);
        }
        fullRoad.moveVehicles();
        check(fullRoad.grid.at(1).north.size() == 1 && fullRoad.grid.at(4).north.isFull(),
              "full downstream lane blocks safely without losing a vehicle");

        TrafficEngine greenLimit(false);
        greenLimit.addTraffic(0, SOUTH, 5); // A's south approach exits north.
        greenLimit.grid.at(0).signalState = NS_GREEN;
        greenLimit.moveVehicles();
        check(greenLimit.cleared == GREEN_LIMIT && greenLimit.grid.at(0).south.size() == 3,
              "two-vehicle green-lane service limit");

        TrafficEngine staged(false);
        Vehicle travelling; travelling.id = 1; travelling.route = "AB"; travelling.destination = 'B';
        staged.grid.at(0).west.enqueue(travelling);
        staged.grid.at(0).signalState = EW_GREEN;
        staged.grid.at(1).signalState = EW_GREEN;
        staged.moveVehicles();
        check(staged.grid.at(1).west.size() == 1 && staged.cleared == 0,
              "ordinary vehicle cannot cross two green intersections in one cycle");

        TrafficEngine rejectedArrival(false);
        rejectedArrival.addTraffic(0, NORTH, LANE_CAPACITY + 1);
        check(rejectedArrival.admitted == LANE_CAPACITY && rejectedArrival.rejected == 1
              && rejectedArrival.grid.at(0).north.isFull(), "full arrival counted as rejected");

        TrafficEngine risk(false);
        risk.addTraffic(0, NORTH, 15);
        risk.updateTelemetry(true);
        risk.updateTelemetry(true);
        check(risk.gridlockEvents == 0, "gridlock grace period");
        risk.updateTelemetry(true);
        risk.updateTelemetry(true);
        check(risk.gridlockEvents == 1, "one penalty per sustained episode");
        while (!risk.grid.at(0).north.isEmpty()) risk.grid.at(0).north.dequeue();
        risk.updateTelemetry(true);
        risk.addTraffic(0, NORTH, 15);
        for (int i = 0; i < 3; ++i) risk.updateTelemetry(true);
        check(risk.gridlockEvents == 2, "recovered intersection can start a new gridlock episode");

        PerformanceReport responsive = runSession("OP-A", true, true, false);
        PerformanceReport repeat = runSession("OP-A", true, true, false);
        PerformanceReport passive = runSession("OP-B", true, false, false);
        check(responsive.cyclesCompleted == 20 && passive.cyclesCompleted == 20, "full competitive sessions");
        check(responsive.vehiclesArrived + responsive.vehiclesRejected == passive.vehiclesArrived + passive.vehiclesRejected,
              "identical deterministic arrival schedule");
        check(responsive.efficiencyIndex == repeat.efficiencyIndex && responsive.vehiclesProcessed == repeat.vehiclesProcessed,
              "fresh session reset and reproducibility");
        check(responsive.efficiencyIndex > passive.efficiencyIndex, "strategy improves performance");
        check(responsive.emergencyCleared == 2, "responsive strategy clears both ambulances");
    }

    // Recommendation tests use isolated states, exercising the new behavior
    // without modifying the original deterministic scenario or demo strategy.
    TrafficRecommendation advice[MAX_RECOMMENDATIONS];
    int adviceCount = 0;
    Vehicle first; first.id = 101; first.route = "BE"; first.destination = 'E';
    {
        TrafficEngine guided(false);
        guided.grid.at(1).signalState = NS_GREEN;
        guided.addTraffic(1, NORTH, 2);
        guided.addTraffic(1, EAST, 3);
        guided.addTraffic(1, WEST, 4);
        int waitingBeforeAdvice = queueTotal(guided.grid.at(1));
        PerformanceReport beforeAdvice = guided.report();
        adviceCount = guided.buildRecommendations(advice);
        check(adviceCount >= 2 && advice[0].action == RECOMMEND_SIGNAL && advice[0].intersection == 1
              && advice[0].signal == EW_GREEN && advice[0].queueDifference == 5,
              "recommend busiest red direction with a clear queue difference");
        check(advice[0].expectedVehicles == 2 * GREEN_LIMIT && advice[0].expectedVehicles == 4,
              "signal estimate respects existing two-per-lane limit");
        check(guided.cycle == 0 && guided.grid.at(1).signalState == NS_GREEN && guided.records.history.empty()
              && guided.plans.isEmpty() && queueTotal(guided.grid.at(1)) == waitingBeforeAdvice
              && guided.report().efficiencyIndex == beforeAdvice.efficiencyIndex,
              "viewing recommendations preserves simulation and scoring");
        TrafficRecommendation signalAdvice = advice[0];
        check(guided.applyRecommendation(signalAdvice) && guided.grid.at(1).signalState == EW_GREEN,
              "apply signal advice without selecting intersection again");
        check(guided.cycle == 0 && guided.cleared == 0 && queueTotal(guided.grid.at(1)) == waitingBeforeAdvice
              && guided.telemetry.signalChanges[1] == 1, "signal apply preserves normal timing and statistics");
        check(!guided.applyRecommendation(signalAdvice) && guided.telemetry.signalChanges[1] == 1,
              "stale signal advice cannot cause repeated changes");
        check(guided.records.history.back().find("[RECOMMENDATION]") != string::npos,
              "applied recommendation appears in existing history");
        guided.moveVehicles();
        check(guided.grid.at(1).vehiclesPassed == 4, "service estimate matches isolated next movement");
    }

    {
        TrafficEngine ordered(false);
        ordered.grid.at(0).signalState = NS_GREEN;
        ordered.grid.at(1).signalState = NS_GREEN;
        ordered.addTraffic(0, EAST, 3);
        ordered.addTraffic(1, EAST, 7);
        ordered.buildRecommendations(advice);
        check(advice[0].intersection == 1 && advice[1].intersection == 0, "signal alternatives sorted by queue imbalance");
    }

    {
        TrafficEngine urgent(false);
        urgent.cycle = 10;
        urgent.roadBlocked = true;
        urgent.grid.at(0).signalState = NS_GREEN;
        urgent.addTraffic(0, EAST, 8);
        urgent.spawnEmergency('D', WEST, "DEFC");
        check(urgent.buildRecommendations(advice) == 1 && advice[0].action == RECOMMEND_EMERGENCY,
              "unprioritized ambulance overrides road and congestion advice");
        check(urgent.applyRecommendation(advice[0]) && urgent.emergencies[0].priorityUntil == 14,
              "emergency advice directly enables existing four-cycle priority");
        urgent.addTraffic(4, NORTH, 9);
        urgent.addTraffic(5, NORTH, 9);
        adviceCount = urgent.buildRecommendations(advice);
        bool corridorSafe = true, duplicateEmergency = false;
        for (int i = 0; i < adviceCount; ++i) {
            if (advice[i].action == RECOMMEND_SIGNAL && urgent.corridorProtects(advice[i].intersection)) corridorSafe = false;
            if (advice[i].action == RECOMMEND_EMERGENCY) duplicateEmergency = true;
        }
        check(corridorSafe, "signal advice preserves active ambulance corridor");
        check(!duplicateEmergency, "already active priority is not recommended again");
        urgent.cycle = 14;
        check(urgent.buildRecommendations(advice) == 1 && advice[0].action == RECOMMEND_EMERGENCY,
              "expiring priority can be renewed for the next cycle");
        urgent.emergencies[0].cleared = true;
        urgent.buildRecommendations(advice);
        check(advice[0].action != RECOMMEND_EMERGENCY, "cleared ambulance is excluded from advice");
    }

    {
        TrafficEngine divertAdvice(false);
        divertAdvice.cycle = 7;
        divertAdvice.roadBlocked = true;
        divertAdvice.grid.at(1).north.enqueue(first);
        divertAdvice.admitted = 1;
        divertAdvice.attemptedWeight = 1;
        divertAdvice.buildRecommendations(advice);
        check(advice[0].action == RECOMMEND_DETOUR && advice[0].detour == 1 && advice[0].expectedVehicles == 1
              && advice[1].action == RECOMMEND_DETOUR && advice[1].detour == 2,
              "accident recommends available predefined detour and alternative");
        check(divertAdvice.applyRecommendation(advice[0]) && divertAdvice.detourChoice == 1
              && divertAdvice.grid.at(1).north.isEmpty() && divertAdvice.grid.at(0).east.size() == 1,
              "apply detour advice executes existing reroute");
        check(divertAdvice.cycle == 7 && divertAdvice.admitted == 1 && divertAdvice.cleared == 0,
              "detour advice preserves vehicle conservation and time");
        adviceCount = divertAdvice.buildRecommendations(advice);
        bool repeatedDiversion = false;
        for (int i = 0; i < adviceCount; ++i)
            if (advice[i].action == RECOMMEND_DETOUR) repeatedDiversion = true;
        check(!repeatedDiversion, "advice respects once-per-cycle diversion allowance");
    }

    {
        TrafficEngine congestedDetour(false);
        congestedDetour.roadBlocked = true;
        congestedDetour.grid.at(1).north.enqueue(first);
        congestedDetour.addTraffic(0, SOUTH, 8);
        congestedDetour.buildRecommendations(advice);
        check(advice[0].action == RECOMMEND_DETOUR && advice[0].detour == 2,
              "less congested alternate route is recommended first");
        congestedDetour.addTraffic(2, WEST, LANE_CAPACITY);
        congestedDetour.buildRecommendations(advice);
        check(advice[0].action == RECOMMEND_DETOUR && advice[0].detour == 1,
              "full diversion entry is not advertised as available");
    }

    {
        TrafficEngine held(false);
        held.roadBlocked = true;
        held.grid.at(1).north.enqueue(first);
        check(held.estimateSignalService(1, NS_GREEN) == 0,
              "service estimate respects front vehicle blocked by accident");
        TrafficEngine fullRoad(false);
        fullRoad.grid.at(1).north.enqueue(first);
        fullRoad.addTraffic(4, NORTH, LANE_CAPACITY);
        check(fullRoad.estimateSignalService(1, NS_GREEN) == 0,
              "service estimate respects full downstream lane");
    }
    {
        TrafficEngine failedAdvice(false);
        failedAdvice.grid.at(4).signalOperational = false;
        failedAdvice.addTraffic(4, EAST, 8);
        adviceCount = failedAdvice.buildRecommendations(advice);
        bool failedSignalSuggested = false;
        for (int i = 0; i < adviceCount; ++i)
            if (advice[i].action == RECOMMEND_SIGNAL && advice[i].intersection == 4) failedSignalSuggested = true;
        check(!failedSignalSuggested && failedAdvice.estimateSignalService(4, EW_GREEN) == 0,
              "failed intersection is not recommended as a signal fix");
    }

    {
        TrafficEngine quiet(false);
        check(quiet.buildRecommendations(advice) == 1 && advice[0].action == RECOMMEND_NEXT,
              "quiet network advises advancing without needless signal changes");
        quiet.cycle = TOTAL_CYCLES;
        quiet.spawnEmergency('F', NORTH, "FC");
        check(quiet.buildRecommendations(advice) == 1 && advice[0].action == RECOMMEND_NEXT,
              "cycle twenty recommends final assessment rather than nonexistent cycle twenty-one");
    }

    // Feedback invariants test conservation independently of the final
    // score: a transfer is an internal arrival, an exit is already a green
    // crossing, and a manual diversion must never be counted as green flow.
    auto balanced = [](const TrafficEngine& sample) {
        int starts = 0, ends = 0, external = 0, internal = 0, passed = 0, exits = 0, diverted = 0;
        const Telemetry& t = sample.telemetry;
        for (int i = 0; i < INTERSECTIONS; ++i) {
            if (t.queueAtCycleStart[i] + t.externalArrivals[i] + t.internalArrivals[i]
                - t.vehiclesPassedSignal[i] - t.divertedOut[i] != t.queueAtCycleEnd[i]) return false;
            if (t.queueAtCycleEnd[i] != queueTotal(sample.grid.at(i))) return false;
            if (t.networkExitsFromIntersection[i] > t.vehiclesPassedSignal[i]) return false;
            starts += t.queueAtCycleStart[i]; ends += t.queueAtCycleEnd[i];
            external += t.externalArrivals[i]; internal += t.internalArrivals[i];
            passed += t.vehiclesPassedSignal[i]; exits += t.networkExitsFromIntersection[i];
            diverted += t.divertedOut[i];
        }
        return starts + external - exits == ends && internal == passed - exits + diverted;
    };
    {
        TrafficEngine movement(false);
        movement.grid.at(0).signalState = EW_GREEN;
        for (int n = 0; n < 3; ++n) {
            Vehicle vehicle; vehicle.id = 101 + n; vehicle.route = n == 0 ? "AB" : "A";
            vehicle.destination = n == 0 ? 'B' : 'X';
            movement.grid.at(0).west.enqueue(vehicle);
        }
        movement.admitted = movement.attemptedWeight = 3;
        movement.resetCycleTraffic();
        movement.addTraffic(0, WEST, 2);
        movement.moveVehicles();
        movement.updateTelemetry(false);
        check(movement.telemetry.queueAtCycleStart[0] == 3 && movement.telemetry.externalArrivals[0] == 2
              && movement.telemetry.vehiclesPassedSignal[0] == 2 && movement.telemetry.queueAtCycleEnd[0] == 3,
              "successful green crossing can leave queue unchanged when arrivals offset it");
        check(movement.telemetry.networkExitsFromIntersection[0] == 1 && movement.cleared == 1
              && movement.telemetry.internalArrivals[1] == 1 && movement.telemetry.externalArrivals[1] == 0,
              "green crossings, network exits and transfers have distinct counters");
        check(balanced(movement), "unchanged queue movement ledger balances");
        string explanation = trafficResultExplanation(movement.telemetry, 0);
        check(explanation.find("successfully moved 2") != string::npos
              && explanation.find("2 vehicles entered") != string::npos
              && explanation.find("pressure stayed the same") != string::npos,
              "unchanged queue explains both successful movement and new arrivals");
        movement.resetCycleTraffic();
        check(movement.telemetry.queueAtCycleStart[0] == 3 && movement.telemetry.externalArrivals[0] == 0
              && movement.telemetry.internalArrivals[1] == 0 && movement.telemetry.vehiclesPassedSignal[0] == 0
              && movement.telemetry.networkExitsFromIntersection[0] == 0,
              "cycle reset captures existing queue and clears all movement counters");
        movement.addTraffic(0, WEST, 3);
        movement.moveVehicles(); movement.updateTelemetry(false);
        check(balanced(movement) && movement.telemetry.queueAtCycleEnd[0] == 4
              && trafficResultExplanation(movement.telemetry, 0).find("pressure rose by 1") != string::npos,
              "growing queue explains arrival pressure despite green movement");
        movement.resetCycleTraffic();
        movement.moveVehicles(); movement.updateTelemetry(false);
        check(balanced(movement) && movement.telemetry.queueAtCycleEnd[0] == 2
              && trafficResultExplanation(movement.telemetry, 0).find("pressure fell by 2") != string::npos,
              "shrinking queue explains successful relief");
    }
    {
        TrafficEngine diversion(false);
        diversion.cycle = 7; diversion.roadBlocked = true;
        diversion.grid.at(1).north.enqueue(first);
        diversion.resetCycleTraffic();
        check(diversion.rerouteTraffic(1) == 1 && diversion.telemetry.divertedOut[1] == 1
              && diversion.telemetry.vehiclesPassedSignal[1] == 0 && diversion.telemetry.internalArrivals[0] == 1
              && diversion.telemetry.networkExitsFromIntersection[1] == 0 && balanced(diversion),
              "manual reroute balances transfers without inventing a green crossing or exit");
        check(trafficResultExplanation(diversion.telemetry, 1).find("manual diversion") != string::npos,
              "diversion is explained separately from signal performance");
        diversion.savePlan();
        diversion.changeSignal(1, NS_GREEN); diversion.restorePlan(false);
        check(balanced(diversion) && diversion.telemetry.divertedOut[1] == 1,
              "plan restoration does not rewind the movement ledger");
    }
    {
        TrafficEngine ambulance(false);
        ambulance.cycle = 18;
        ambulance.resetCycleTraffic();
        ambulance.grid.at(5).signalState = NS_GREEN;
        ambulance.spawnEmergency('F', NORTH, "FC");
        check(ambulance.telemetry.externalArrivals[5] == 1, "accepted ambulance is a new city arrival");
        ambulance.moveVehicles(); ambulance.updateTelemetry(false);
        check(ambulance.telemetry.vehiclesPassedSignal[5] == 1
              && ambulance.telemetry.networkExitsFromIntersection[5] == 1
              && ambulance.telemetry.internalArrivals[2] == 0 && ambulance.cleared == 1 && balanced(ambulance),
              "hospital completion records exactly one exit at the source intersection");
    }
    {
        TrafficEngine full(false);
        full.addTraffic(0, NORTH, LANE_CAPACITY);
        full.resetCycleTraffic();
        full.addTraffic(0, NORTH, 1); full.updateTelemetry(false);
        check(full.telemetry.queueAtCycleStart[0] == LANE_CAPACITY && full.telemetry.externalArrivals[0] == 0
              && full.rejected == 1 && balanced(full), "rejected traffic never appears as an accepted arrival");
        full.spawnEmergency('A', NORTH, "ABC"); full.updateTelemetry(false);
        check(full.telemetry.externalArrivals[0] == 0 && full.rejected == 2 && balanced(full),
              "rejected ambulance does not inflate arrival feedback");
    }
    {
        TrafficEngine focus(false);
        focus.previousHotspot = 1; focus.feedbackIntersection = 4;
        focus.telemetry.queueAtCycleEnd[6] = 8;
        int selected[MAX_TRAFFIC_RESULTS];
        int count = focus.selectTrafficResultIntersections(selected);
        check(count == 3 && selected[0] == 1 && selected[1] == 4 && selected[2] == 6,
              "automatic feedback prioritizes previous hotspot, recommendation and significant change");
        focus.feedbackIntersection = 1;
        count = focus.selectTrafficResultIntersections(selected);
        check(count == 2 && selected[0] == 1 && selected[1] == 6, "automatic feedback deduplicates intersections");
        focus.feedbackIntersection = -1; focus.telemetry.queueAtCycleEnd[6] = 0;
        check(focus.selectTrafficResultIntersections(selected) == 1, "quiet feedback shows only one intersection");
        focus.advanceCycle();
        focus.buildRecommendations(advice);
        check(focus.pendingRecommendationIntersection == -1, "viewing advice does not affect movement report selection");
        int recommended = advice[0].intersection;
        check(focus.applyRecommendation(advice[0]) && focus.pendingRecommendationIntersection == recommended,
              "applied signal recommendation marks its intersection for next-cycle feedback");
        int queueBefore = queueTotal(focus.grid.at(recommended));
        focus.advanceCycle();
        check(focus.feedbackIntersection == recommended && focus.telemetry.queueAtCycleStart[recommended] == queueBefore
              && focus.pendingRecommendationIntersection == -1, "recommended action feedback follows the next real cycle");
        focus.advanceCycle();
        check(focus.feedbackIntersection == -1, "recommendation feedback is not repeated across unrelated cycles");
        focus.executeCommand("SIGNAL:B:EW"); focus.advanceCycle();
        check(focus.feedbackIntersection == 1, "manual signal action also gets next-cycle movement feedback");
    }



    
    // Check every intersection during two entire scenarios, including all
    // arrivals, incidents, emergency completions and after-cycle diversions.
    for (int strategy = 0; strategy < 2; ++strategy) {
        TrafficEngine scenario(false);
        for (int step = 0; step < TOTAL_CYCLES; ++step) {
            int beforeAdmitted = scenario.admitted, beforeExits = scenario.cleared;
            int beforeGreen = scenario.greenCrossings;
            scenario.advanceCycle();
            int external = 0, exits = 0, passed = 0;
            for (int i = 0; i < INTERSECTIONS; ++i) {
                external += scenario.telemetry.externalArrivals[i];
                exits += scenario.telemetry.networkExitsFromIntersection[i];
                passed += scenario.telemetry.vehiclesPassedSignal[i];
            }
            check(balanced(scenario) && external == scenario.admitted - beforeAdmitted
                  && exits == scenario.cleared - beforeExits && passed == scenario.greenCrossings - beforeGreen,
                  "full scenario movement counters reconcile with all queues and global totals");
            if (strategy == 1 && step + 1 < TOTAL_CYCLES) {
                scenario.responsiveStrategy();
                check(balanced(scenario), "responsive operator diversions preserve the current cycle ledger");
            }
        }
        check(!scenario.advanceCycle() && balanced(scenario), "cycle limit preserves the last completed movement result");
    }
    cout << "SELF-TEST: " << checks - failures << " / " << checks << " checks passed.\n";
    return failures == 0;
}

// ============================================================
// MAIN FUNCTION
// ============================================================
int main(int argc, char* argv[]) {
    if (argc > 1) {
        string mode = argv[1];
        if (mode == "--self-test") return runSelfTests() ? 0 : 1;
        if (mode == "--demo") { runSession("DEMO OPERATOR", true, true); return 0; }
        if (mode == "--demo-compare") {
            cout << "Responsive operator A versus passive operator B; identical 20-cycle scenario.\n";
            PerformanceReport a = runSession("OP-A", true, true);
            PerformanceReport b = runSession("OP-B", true, false);
            compareReports(a, b);
            return 0;
        }
        cout << "Usage: gridlock [--demo | --demo-compare | --self-test]\n";
        return 1;
    }
    startup();
    while (!inputClosed) {
        cout << "\n\n1. SINGLE OPERATOR\n2. COMPETITIVE COMPARISON\n0. EXIT\n";
        int choice = readMenu(0, 2);
        if (choice <= 0) break;
        if (choice == 1) runSession("SINGLE OPERATOR");
        else {
            PerformanceReport a = runSession("OP-A");
            if (inputClosed) break;
            cout << "\nOPERATOR B receives a fresh city and the same scheduled traffic and incidents.\n";
            PerformanceReport b = runSession("OP-B");
            if (!inputClosed) compareReports(a, b);
        }
    }
    cout << "\nGRIDLOCK-X session closed.\n";
    return 0;
}
