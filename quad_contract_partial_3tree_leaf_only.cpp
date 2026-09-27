// quad_contract_partial_3tree_leaf_only.cpp
//
// Standalone checker. In plain language, it:
//   1. reads a planar graph whose faces should all have four sides,
//   2. tries safely shrinking edges without changing the list of faces, and
//   3. accepts if the remaining graph can be completed to a planar 3-tree.
// It tries at most floor(number of faces / 2) contractions. Optional SVG files
// show the original graph, the contracted graph, and a completed 3-tree.
//
// For the final recognition step, "partial 3-tree" is tested as treewidth <= 3
// using an exact elimination-order search with fill edges. Since the graph is
// maintained as a planar embedded graph through face-maintaining contractions,
// this is the intended partial planar 3-tree check.

#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <functional>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifdef USE_OGDF
#include <ogdf/basic/CombinatorialEmbedding.h>
#include <ogdf/basic/Graph.h>
#endif

using namespace std;
namespace fs = std::filesystem;

using VID = int;

// A planar embedding is more than a list of connections: at every vertex we
// must also know the clockwise order of its neighbors. That order lets us find
// the faces and must be preserved when an edge is contracted.
struct Graph {
    int N = 0;
    vector<string> name; // name of vertices (when contracted, names are merged)
    vector<set<VID>> members; // original vertices merged into this vertex
    vector<bool> alive;       // false after a vertex has been contracted away
    vector<vector<VID>> adj;  // neighbors in clockwise order

    int indexOf(VID v, VID w) const {
        for (int i = 0; i < (int)adj[v].size(); i++) {
            if (adj[v][i] == w) return i;
        }
        return -1;
    }

    bool hasEdge(VID u, VID v) const {
        if (u < 0 || u >= N || v < 0 || v >= N) return false;
        if (!alive[u] || !alive[v]) return false;
        return indexOf(u, v) != -1;
    }

    VID cwNext(VID v, VID w) const {
        int i = indexOf(v, w);
        int n = (int)adj[v].size();
        return adj[v][(i + 1) % n];
    }

    vector<VID> aliveVertices() const {
        vector<VID> out;
        for (int i = 0; i < N; i++) if (alive[i]) out.push_back(i);
        return out;
    }

    vector<vector<VID>> faces() const {
        // Walk along each directed edge once. On reaching vertex cv from cu,
        // taking the next clockwise edge keeps the same face on one side.
        set<pair<VID,VID>> visited;
        vector<vector<VID>> out;
        for (VID u : aliveVertices()) {
            for (VID v : adj[u]) {
                if (v < 0 || v >= N || !alive[v]) continue;
                if (visited.count({u, v})) continue;
                vector<VID> f;
                VID cu = u, cv = v;
                do {
                    visited.insert({cu, cv});
                    f.push_back(cu);
                    VID nv = cwNext(cv, cu); // vertices of the face in clockwise order
                    cu = cv;
                    cv = nv;
                } while (cu != u || cv != v);
                out.push_back(f);
            }
        }
        return out;
    }
};

// ---------------------------------------------------------------------------
// Input and small graph utilities
// ---------------------------------------------------------------------------

static pair<VID,VID> edgeKey(VID a, VID b) {
    // Store an undirected edge in one consistent order, smaller endpoint first.
    return (a < b) ? make_pair(a, b) : make_pair(b, a);
}

static bool isBlankLine(const string& s) {
    // Return true when a line contains no visible characters.
    for (char c : s) if (!isspace((unsigned char)c)) return false;
    return true;
}

static Graph parseASCII(const string& input) {
    // Example: "4 bd,ac,bd,ac" means four vertices a-d; each comma-separated
    // group lists one vertex's neighbors in clockwise order.
    istringstream ss(input);
    int N;
    ss >> N;
    string rest;
    getline(ss, rest);
    while (!rest.empty() && isspace((unsigned char)rest[0])) rest.erase(rest.begin());

    vector<string> parts;
    string cur;
    for (char c : rest) {
        if (c == ',') {
            parts.push_back(cur);
            cur.clear();
        } else {
            cur.push_back(c);
        }
    }
    parts.push_back(cur);

    if ((int)parts.size() != N) {
        throw runtime_error("input does not contain exactly N adjacency lists");
    }

    Graph G;
    G.N = N;
    G.name.resize(N);
    G.members.resize(N);
    G.alive.assign(N, true);
    G.adj.resize(N);
    for (int i = 0; i < N; i++) {
        // The ASCII format numbers vertices with consecutive byte values
        // starting at 'a'. For graphs larger than 31 vertices, those values
        // exceed 0x7f, so preserve the byte explicitly instead of relying on
        // whether plain char is signed on this platform.
        G.name[i] = string(1, static_cast<char>(static_cast<unsigned char>('a') + i));
        G.members[i].insert(i);
        for (char c : parts[i]) {
            if (isspace((unsigned char)c)) continue;
            VID v = static_cast<unsigned char>(c) - static_cast<unsigned char>('a');
            if (v < 0 || v >= N) throw runtime_error("invalid vertex name in adjacency list");
            G.adj[i].push_back(v);
        }
    }
    return G;
}

static vector<pair<VID,VID>> aliveEdges(const Graph& G) {
    // List every edge between active vertices exactly once.
    vector<pair<VID,VID>> out;
    set<pair<VID,VID>> seen;
    for (VID u : G.aliveVertices()) {
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) continue;
            auto k = edgeKey(u, v);
            if (seen.insert(k).second) out.push_back(k);
        }
    }
    return out;
}

static string graphStateKey(const Graph& G) {
    // A stable text description used to avoid solving the exact same search
    // state more than once.
    ostringstream os;
    os << "A";
    for (int i = 0; i < G.N; i++) os << (G.alive[i] ? '1' : '0');
    os << ";";
    for (int u = 0; u < G.N; u++) {
        if (!G.alive[u]) continue;
        os << u << ":";
        for (VID v : G.adj[u]) if (v >= 0 && v < G.N && G.alive[v]) os << v << ",";
        os << ";";
    }
    return os.str();
}

static string canonicalCycle(vector<string> labels) {
    // A face has no fixed starting corner or direction. Choose the smallest (lexicographically) of
    // all rotations and reversals so equivalent face boundaries compare equal.
    int n = (int)labels.size();
    if (n == 0) return "";
    vector<string> best;
    bool haveBest = false;
    for (int rev = 0; rev < 2; rev++) {
        vector<string> cur = labels;
        if (rev) reverse(cur.begin(), cur.end());
        for (int shift = 0; shift < n; shift++) {
            vector<string> candidate;
            for (int i = 0; i < n; i++) candidate.push_back(cur[(shift + i) % n]);
            if (!haveBest || candidate < best) {
                best = candidate;
                haveBest = true;
            }
        }
    }
    ostringstream os;
    for (int i = 0; i < n; i++) {
        if (i) os << "|";
        os << best[i];
    }
    return os.str();
}

static string vertexMemberLabel(const Graph& G, VID v) {
    // Turn a merged vertex's original IDs into a stable label such as "0,2,5".
    ostringstream os;
    bool first = true;
    for (VID x : G.members[v]) {
        if (!first) os << ",";
        first = false;
        os << x;
    }
    return os.str();
}

static string canonicalFaceByMembers(const Graph& G, const vector<VID>& face) {
    // Describe one face independently of its starting corner and direction.
    vector<string> labels;
    for (VID v : face) labels.push_back(vertexMemberLabel(G, v));
    return canonicalCycle(labels);
}

static multiset<string> faceMultisetByMembers(const Graph& G) {
    // Describe all faces; a multiset preserves repeated equal boundaries.
    multiset<string> out;
    for (const auto& face : G.faces()) {
        if (face.size() >= 3) out.insert(canonicalFaceByMembers(G, face));
    }
    return out;
}

static bool adjacencySymmetric(const Graph& G) {
    // Every edge u-v must occur once at u and once at v.
    for (VID u : G.aliveVertices()) {
        set<VID> seen;
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) return false;
            if (!seen.insert(v).second) return false;
            if (G.indexOf(v, u) == -1) return false;
        }
    }
    return true;
}

static Graph contractEdge(const Graph& G, VID u, VID v) {
    // Shrink u-v by keeping u and removing v. The neighbors formerly around v
    // are spliced into u's clockwise list at the position of edge u-v.
    Graph H = G;
    int posU = H.indexOf(u, v); // position of v in u's list
    int posV = H.indexOf(v, u);
    int dv = (int)H.adj[v].size();

    vector<VID> insert; // neighbors of v to insert into u's list, in clockwise order
    for (int i = 1; i < dv; i++) {
        VID w = H.adj[v][(posV + i) % dv];
        if (w != u) insert.push_back(w);
    }

    H.adj[u].erase(H.adj[u].begin() + posU); // remove v from u's list
    H.adj[u].insert(H.adj[u].begin() + posU, insert.begin(), insert.end()); // splice in v's neighbors

    for (VID w : insert) {
        int pw = H.indexOf(w, v);
        if (pw != -1) H.adj[w][pw] = u;
    }

    H.members[u].insert(H.members[v].begin(), H.members[v].end());
    string mergedName;
    for (VID x : H.members[u]) {
        mergedName += string(1, static_cast<char>(static_cast<unsigned char>('a') + x));
    }
    H.name[u] = mergedName;
    H.members[v].clear();
    H.adj[v].clear();
    H.alive[v] = false;
    return H;
}

static bool isFaceMaintainingContraction(const Graph& G, VID u, VID v) {
    if (!G.hasEdge(u, v)) return false;

    // Minimal test: a common neighbor would create parallel edges and collapse
    // the triangle through that neighbor. No additional face/symmetry replay is
    // performed in this experimental version.
    for (VID w : G.adj[u]) {
        if (w != v && G.hasEdge(v, w)) return false;
    }
    return true;
}

static string canonicalEdgeByMembers(const Graph& G, VID u, VID v) {
    // Describe an edge using the original vertices inside its current endpoints.
    string a = vertexMemberLabel(G, u);
    string b = vertexMemberLabel(G, v);
    if (b < a) swap(a, b);
    return a + "--" + b;
}

static multiset<string> edgeMultisetByMembers(const Graph& G) {
    // Describe all current edges in a way that survives endpoint renaming.
    multiset<string> out;
    for (auto [u, v] : aliveEdges(G)) {
        out.insert(canonicalEdgeByMembers(G, u, v));
    }
    return out;
}

static bool validateInputGraph(const Graph& G, string& message) {
    // Check the basic invariants required by all later embedding algorithms.
    if (!adjacencySymmetric(G)) {
        message = "adjacency lists are not symmetric, contain duplicates, or reference dead/invalid vertices";
        return false;
    }
    for (VID u : G.aliveVertices()) {
        if (G.hasEdge(u, u)) {
            message = "loop edge detected";
            return false;
        }
    }
    // Force face traversal once after symmetry validation; this catches broken
    // rotation systems early instead of deep inside the search.
    (void)G.faces();
    return true;
}

static bool testOneContractionDirection(const Graph& G, VID u, VID v, ostream& out, bool& tested) {
    // Diagnostic: compare keeping u versus keeping v when shrinking the same edge.
    bool uvMaint = isFaceMaintainingContraction(G, u, v);
    bool vuMaint = isFaceMaintainingContraction(G, v, u);
    tested = uvMaint || vuMaint;
    if (!tested) return true;

    Graph uv = contractEdge(G, u, v);
    Graph vu = contractEdge(G, v, u);
    bool uvSym = adjacencySymmetric(uv);
    bool vuSym = adjacencySymmetric(vu);
    bool sameEdges = uvSym && vuSym && edgeMultisetByMembers(uv) == edgeMultisetByMembers(vu);
    bool sameFaces = uvSym && vuSym && faceMultisetByMembers(uv) == faceMultisetByMembers(vu);
    if (uvMaint != vuMaint || (uvMaint && vuMaint && (uvSym != vuSym || !sameEdges || !sameFaces))) {
        out << "  contraction direction mismatch on edge "
            << G.name[edgeKey(u, v).first] << G.name[edgeKey(u, v).second]
            << " (sym " << uvSym << "/" << vuSym
            << ", faceMaintaining " << uvMaint << "/" << vuMaint
            << ", sameEdges " << sameEdges
            << ", sameFaces " << sameFaces << ")\n";
        return false;
    }
    return true;
}

static bool testContractionDirectionConsistency(const Graph& G, int maxDepth, ostream& out) {
    // Diagnostic only: shrinking u into v or v into u should describe the same
    // embedded result, apart from which endpoint name survives.
    bool ok = true;
    long long states = 0;
    long long tested = 0;
    unordered_map<string,bool> seen;

    function<void(const Graph&, int)> dfs = [&](const Graph& cur, int depth) {
        string key = to_string(depth) + "|" + graphStateKey(cur);
        if (seen.count(key)) return;
        seen[key] = true;
        states++;
        for (auto [u, v] : aliveEdges(cur)) {
            bool didTest = false;
            if (!testOneContractionDirection(cur, u, v, out, didTest)) ok = false;
            if (didTest) tested++;
        }
        if (depth == maxDepth) return;
        set<string> seenNext;
        for (auto [u, v] : aliveEdges(cur)) {
            if (!isFaceMaintainingContraction(cur, u, v)) continue;
            Graph next = contractEdge(cur, u, v);
            string nk = graphStateKey(next);
            if (!seenNext.insert(nk).second) continue;
            dfs(next, depth + 1);
        }
    };

    dfs(G, 0);
    out << "  contraction direction tests: " << tested
        << " directed-state edge checks across " << states
        << " reachable states, " << (ok ? "PASS" : "FAIL") << "\n";
    return ok;
}

static string twStateKey(const vector<set<int>>& adj, const vector<int>& alive) {
    // Serialize one treewidth-search state for failed-state memoization.
    ostringstream os;
    os << "A";
    for (int x : alive) os << x << ",";
    os << ";E";
    for (int u : alive) {
        os << u << ":";
        for (int v : adj[u]) if (binary_search(alive.begin(), alive.end(), v)) os << v << ",";
        os << ";";
    }
    return os.str();
}

struct CompletionResult {
    bool ok = false;
    set<pair<VID,VID>> addedEdges;
};

// ---------------------------------------------------------------------------
// Partial 3-tree test (equivalently: treewidth at most 3)
//
// Eliminate vertices one at a time. A vertex is eligible when it has at most
// three remaining neighbors. Before removing it, connect those neighbors to
// one another (the "fill edges"). If some elimination order removes the whole
// graph, the graph is a partial 3-tree.
// ---------------------------------------------------------------------------

static bool completionDfs(vector<set<int>> adj, vector<int> alive,
                          const vector<VID>& originalVertex,
                          unordered_map<string,bool>& dead,
                          set<pair<VID,VID>>& addedEdges) {
    sort(alive.begin(), alive.end());

    if (alive.size() <= 4) {
        // Any graph on at most four vertices fits inside a complete K4.
        for (int i = 0; i < (int)alive.size(); i++) {
            for (int j = i + 1; j < (int)alive.size(); j++) {
                int a = alive[i], b = alive[j];
                if (!adj[a].count(b)) {
                    addedEdges.insert(edgeKey(originalVertex[a], originalVertex[b]));
                    adj[a].insert(b);
                    adj[b].insert(a);
                }
            }
        }
        return true;
    }

    string key = twStateKey(adj, alive);
    if (dead.count(key)) return false;

    set<int> aliveSet(alive.begin(), alive.end());
    vector<int> candidates;
    for (int v : alive) { // eligible vertices have at most three remaining neighbors
        int d = 0;
        for (int w : adj[v]) if (aliveSet.count(w)) d++;
        if (d <= 3) candidates.push_back(v);
    }

    sort(candidates.begin(), candidates.end(), [&](int a, int b) { // prefer vertices with fewer remaining neighbors
        int da = 0, db = 0;
        for (int w : adj[a]) if (aliveSet.count(w)) da++;
        for (int w : adj[b]) if (aliveSet.count(w)) db++;
        return da < db;
    });

    for (int v : candidates) {
        vector<int> nb;
        for (int w : adj[v]) if (aliveSet.count(w)) nb.push_back(w);

        // Make v's remaining neighbors a clique, then delete v. Recursion tries
        // every eligible choice because a poor early choice can get stuck.
        auto nextAdj = adj;
        set<pair<VID,VID>> localAdded;
        for (int i = 0; i < (int)nb.size(); i++) {
            for (int j = i + 1; j < (int)nb.size(); j++) {
                if (!nextAdj[nb[i]].count(nb[j])) {
                    localAdded.insert(edgeKey(originalVertex[nb[i]], originalVertex[nb[j]]));
                    nextAdj[nb[i]].insert(nb[j]);
                    nextAdj[nb[j]].insert(nb[i]);
                }
            }
        }
        for (int w : nb) nextAdj[w].erase(v);
        nextAdj[v].clear();

        vector<int> nextAlive;
        for (int x : alive) if (x != v) nextAlive.push_back(x);

        set<pair<VID,VID>> childAdded;
        if (completionDfs(nextAdj, nextAlive, originalVertex, dead, childAdded)) {
            addedEdges.insert(localAdded.begin(), localAdded.end());
            addedEdges.insert(childAdded.begin(), childAdded.end());
            return true;
        }
    }

    dead[key] = false;
    return false;
}

static CompletionResult partial3TreeCompletion(const Graph& G) {
    // Run the readable set-based treewidth test and also return its fill edges.
    CompletionResult result;
    vector<VID> verts = G.aliveVertices();
    if (verts.empty()) {
        result.ok = true;
        return result;
    }

    map<VID,int> remap;
    for (int i = 0; i < (int)verts.size(); i++) remap[verts[i]] = i;

    int n = (int)verts.size();
    vector<set<int>> adj(n);
    for (VID u : verts) { 
        int su = remap[u]; 
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) continue;
            adj[su].insert(remap[v]);
        }
    } 

    vector<int> alive(n);
    for (int i = 0; i < n; i++) alive[i] = i;
    unordered_map<string,bool> dead;
    result.ok = completionDfs(adj, alive, verts, dead, result.addedEdges);
    return result;
}

struct Tw3BitKey {
    // Compact treewidth-search state: one bit per active vertex and neighbor.
    uint64_t alive = 0;
    vector<uint64_t> adj;

    bool operator==(const Tw3BitKey& other) const {
        return alive == other.alive && adj == other.adj;
    }
};

struct Tw3BitKeyHash {
    // Combine all state bits so Tw3BitKey can be stored in an unordered_map.
    size_t operator()(const Tw3BitKey& key) const {
        uint64_t h = key.alive * 11400714819323198485ull;
        for (uint64_t x : key.adj) {
            h ^= x + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
        }
        return (size_t)h;
    }
};

static bool partial3TreeBitsetDfs(vector<uint64_t> adj,
                                  uint64_t alive,
                                  unordered_map<Tw3BitKey,bool,Tw3BitKeyHash>& dead) {
    if (__builtin_popcountll(alive) <= 4) return true;

    Tw3BitKey key{alive, adj};
    if (dead.count(key)) return false;

    vector<pair<int,int>> candidates;
    uint64_t remaining = alive; 
    while (remaining) {
        int v = __builtin_ctzll(remaining);
        remaining &= remaining - 1; // clear the lowest set bit
        int degree = __builtin_popcountll(adj[v] & alive);
        if (degree <= 3) candidates.push_back({degree, v});
    }

    sort(candidates.begin(), candidates.end()); // prefer vertices with fewer remaining neighbors

    for (auto [degree, v] : candidates) {
        (void)degree;
        uint64_t nbMask = adj[v] & alive;
        vector<int> neighbors;
        uint64_t x = nbMask;
        while (x) { // collect the indices of the set bits in nbMask
            int w = __builtin_ctzll(x);
            x &= x - 1;
            neighbors.push_back(w);
        }

        vector<uint64_t> nextAdj = adj;
        for (int i = 0; i < (int)neighbors.size(); i++) { // make neighbors a clique
            for (int j = i + 1; j < (int)neighbors.size(); j++) {
                nextAdj[neighbors[i]] |= 1ull << neighbors[j];
                nextAdj[neighbors[j]] |= 1ull << neighbors[i];
            }
        }
        for (int w : neighbors) nextAdj[w] &= ~(1ull << v); // remove v from neighbors' adjacency
        nextAdj[v] = 0;

        if (partial3TreeBitsetDfs(nextAdj, alive & ~(1ull << v), dead)) return true;
    }

    dead[key] = false;
    return false;
}

static bool partial3TreeCompletionFastBool(const Graph& G) {
    // Same exact search as completionDfs, packed into bits for speed. This
    // version answers only yes/no; the set-based version also records fill edges.
    vector<VID> verts = G.aliveVertices();
    int n = (int)verts.size();
    if (n <= 4) return true;

    // The fast path uses one uint64_t bit per alive vertex. This project only
    // uses small quadrangulations, but keep the old exact checker as fallback.
    if (n > 63) return partial3TreeCompletion(G).ok;

    map<VID,int> remap;
    for (int i = 0; i < n; i++) remap[verts[i]] = i;

    vector<uint64_t> adj(n, 0);
    for (VID u : verts) {
        int su = remap[u];
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) continue;
            adj[su] |= 1ull << remap[v]; // set the bit for neighbor v
        }
    }

    uint64_t alive = (1ull << n) - 1; // all alive vertices are initially present
    unordered_map<Tw3BitKey,bool,Tw3BitKeyHash> dead;
    return partial3TreeBitsetDfs(adj, alive, dead);
}

static string toCompactASCII(const Graph& G) {
    // Print the active graph in the program's input format with fresh a,b,c... names.
    vector<VID> verts = G.aliveVertices();
    map<VID,int> remap;
    for (int i = 0; i < (int)verts.size(); i++) remap[verts[i]] = i;

    ostringstream os;
    os << verts.size() << " ";
    for (int i = 0; i < (int)verts.size(); i++) {
        if (i) os << ",";
        VID old = verts[i];
        for (VID nb : G.adj[old]) {
            if (nb < 0 || nb >= G.N || !G.alive[nb]) continue;
            os << static_cast<char>(static_cast<unsigned char>('a') + remap[nb]);
        }
    }
    return os.str();
}

static string toOriginalLabelASCII(const Graph& G) {
    // Print the active graph while showing which original vertices were merged.
    vector<VID> verts = G.aliveVertices();
    ostringstream os;
    os << verts.size() << " ";
    for (int i = 0; i < (int)verts.size(); i++) {
        if (i) os << ",";
        VID u = verts[i];
        os << G.name[u] << ":";
        for (VID nb : G.adj[u]) {
            if (nb < 0 || nb >= G.N || !G.alive[nb]) continue;
            os << G.name[nb];
        }
    }
    return os.str();
}

static string faceNames(const Graph& G, const vector<VID>& face) {
    // Format a face boundary for human-readable output, for example a-b-c-d.
    string out;
    for (VID v : face) {
        if (v < 0 || v >= G.N) continue;
        if (!out.empty()) out += "-";
        out += G.name[v];
    }
    return out;
}

static pair<VID,VID> originalEdgeWitness(const Graph& original, const Graph& cur, VID u, VID v) {
    // Find an original input edge that explains a contraction between two
    // vertices that may themselves already contain several original vertices.
    for (VID a : cur.members[u]) {
        for (VID b : cur.members[v]) {
            if (original.hasEdge(a, b)) return edgeKey(a, b);
        }
    }
    return edgeKey(u, v);
}

static string edgeName(const Graph& G, pair<VID,VID> e) {
    // Format an edge using its two printable endpoint names.
    return G.name[e.first] + G.name[e.second];
}

static bool findMatchingFace(const Graph& G, const vector<VID>& preferred, vector<VID>& matched);

static vector<VID> transformedFaceAfterContractions(const Graph& originalGraph,
                                                    vector<VID> face,
                                                    const vector<pair<VID,VID>>& directedContractions) {
    // Follow a chosen face through a sequence of contractions so drawings can
    // keep roughly the same outer boundary from one stage to the next.
    Graph cur = originalGraph;
    for (auto [kept, removed] : directedContractions) {
        for (VID& v : face) {
            if (v == removed) v = kept;
        }
        vector<VID> cleaned;
        for (VID v : face) {
            if (cleaned.empty() || cleaned.back() != v) cleaned.push_back(v);
        }
        if (cleaned.size() > 1 && cleaned.front() == cleaned.back()) cleaned.pop_back();
        face.swap(cleaned);

        cur = contractEdge(cur, kept, removed);

        vector<VID> matched;
        if (!face.empty() && findMatchingFace(cur, face, matched)) {
            face = matched;
        }
    }

    vector<VID> cleaned;
    for (VID v : face) {
        if (v < 0 || v >= cur.N || !cur.alive[v]) continue;
        if (cleaned.empty() || cleaned.back() != v) cleaned.push_back(v);
    }
    if (cleaned.size() > 1 && cleaned.front() == cleaned.back()) cleaned.pop_back();
    if (cleaned.size() < 3) cleaned.clear();
    vector<VID> matched;
    if (!cleaned.empty() && findMatchingFace(cur, cleaned, matched)) return matched;
    return cleaned;
}

static bool consecutiveInBoundary(const vector<VID>& boundary, VID a, VID b) {
    // Return true if a-b is one of the boundary's sides, including the last-first side.
    int n = (int)boundary.size();
    for (int i = 0; i < n; i++) {
        if (edgeKey(boundary[i], boundary[(i + 1) % n]) == edgeKey(a, b)) return true;
    }
    return false;
}

static vector<VID> completionOuterBoundary(const Graph& completedGraph,
                                           const vector<VID>& oldBoundary,
                                           const set<pair<VID,VID>>& addedEdges) {
    // Choose the face that best continues the old outer boundary after added
    // diagonals may have split that boundary into several triangular faces.
    if (oldBoundary.size() < 3) return oldBoundary;

    set<VID> boundarySet(oldBoundary.begin(), oldBoundary.end());
    bool changedByOuterDiagonal = false;
    for (auto [u, v] : addedEdges) {
        if (boundarySet.count(u) && boundarySet.count(v) &&
            !consecutiveInBoundary(oldBoundary, u, v)) {
            changedByOuterDiagonal = true;
            break;
        }
    }
    if (!changedByOuterDiagonal) return oldBoundary;

    vector<VID> best;
    int bestScore = -1;
    for (const auto& face : completedGraph.faces()) {
        bool allOnOldBoundary = true;
        for (VID v : face) {
            if (!boundarySet.count(v)) {
                allOnOldBoundary = false;
                break;
            }
        }
        if (!allOnOldBoundary) continue;

        int score = 0;
        for (int i = 0; i < (int)face.size(); i++) {
            if (consecutiveInBoundary(oldBoundary, face[i], face[(i + 1) % face.size()])) score++;
        }
        if (score > bestScore || (score == bestScore && face.size() > best.size())) {
            bestScore = score;
            best = face;
        }
    }

    return best.empty() ? oldBoundary : best;
}

struct SearchResult {
    bool found = false;
    vector<string> contractions;
    vector<pair<VID,VID>> contractionEdges;
    vector<pair<VID,VID>> directedContractions;
    Graph finalGraph;
};

// ---------------------------------------------------------------------------
// Search over valid edge contractions
// ---------------------------------------------------------------------------

static SearchResult searchContractions(const Graph& G, int targetDepth) {
    SearchResult result;
    unordered_set<string> dead;
    Graph finalGraph;

    function<bool(const Graph&, int, vector<string>&)> dfs =
        [&](const Graph& cur, int depth, vector<string>& path) -> bool {
            string key = to_string(targetDepth - depth) + "|" + graphStateKey(cur);
            if (dead.count(key)) return false;

            // Test only at this branch's leaf: either the global contraction
            // limit, or a state from which no legal contraction is available.
            if (depth == targetDepth) {
                if (partial3TreeCompletionFastBool(cur)) {
                    finalGraph = cur;
                    return true;
                }
                dead.insert(key);
                return false;
            }

            // Depth-first search tries every legal next edge. Duplicate states
            // and already-failed states are skipped to keep the search practical.
            set<string> seenNext;
            bool hasChild = false;
            for (auto [u, v] : aliveEdges(cur)) {
                if (!isFaceMaintainingContraction(cur, u, v)) continue;
                pair<VID,VID> witness = originalEdgeWitness(G, cur, u, v);
                Graph next = contractEdge(cur, u, v);
                string nk = graphStateKey(next);
                if (!seenNext.insert(nk).second) continue;
                hasChild = true;

                path.push_back(edgeName(G, witness));
                result.contractionEdges.push_back(witness);
                result.directedContractions.push_back({u, v});
                if (dfs(next, depth + 1, path)) return true;
                result.directedContractions.pop_back();
                result.contractionEdges.pop_back();
                path.pop_back();
            }

            if (!hasChild && partial3TreeCompletionFastBool(cur)) {
                finalGraph = cur;
                return true;
            }

            dead.insert(key);
            return false;
        };

    vector<string> path;
    result.found = dfs(G, 0, path);
    if (result.found) {
        result.contractions = path;
        result.finalGraph = finalGraph;
    }
    return result;
}

#ifdef USE_OGDF
// Optional independent check: replay the reported contractions in the OGDF
// graph library and confirm that the face count and final graph agree.
static bool ogdfHasSelfLoopOrParallelEdge(const ogdf::Graph& OG, string& message) {
    // Reject structures that would no longer be a simple graph.
    set<pair<int,int>> seenEdges;
    for (ogdf::edge e = OG.firstEdge(); e != nullptr; e = e->succ()) {
        int a = e->source()->index();
        int b = e->target()->index();
        if (a == b) {
            message = "OGDF graph has a self-loop";
            return true;
        }
        if (b < a) swap(a, b);
        if (!seenEdges.insert({a, b}).second) {
            message = "OGDF graph has parallel edges";
            return true;
        }
    }
    return false;
}

static ogdf::edge findOgdfEdgeBetween(const vector<ogdf::node>& nodeOf, VID u, VID v) {
    // Find OGDF's edge object corresponding to the program's vertex IDs.
    if (u < 0 || u >= (VID)nodeOf.size() || v < 0 || v >= (VID)nodeOf.size()) return nullptr;
    ogdf::node nu = nodeOf[u];
    ogdf::node nv = nodeOf[v];
    if (nu == nullptr || nv == nullptr) return nullptr;
    for (ogdf::adjEntry adj : nu->adjEntries) {
        if (adj->twinNode() == nv) return adj->theEdge();
    }
    return nullptr;
}

static bool buildOgdfGraphWithRotation(const Graph& G,
                                       ogdf::Graph& OG,
                                       vector<ogdf::node>& nodeOf,
                                       string& message) {
    // Copy the graph and its clockwise neighbor orders into OGDF.
    nodeOf.assign(G.N, nullptr);
    for (VID v : G.aliveVertices()) {
        nodeOf[v] = OG.newNode();
    }

    for (auto [u, v] : aliveEdges(G)) {
        OG.newEdge(nodeOf[u], nodeOf[v]);
    }

    for (VID u : G.aliveVertices()) {
        vector<ogdf::adjEntry> order;
        set<VID> seen;
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) continue;
            if (!seen.insert(v).second) {
                message = "duplicate neighbor while building OGDF rotation";
                return false;
            }
            ogdf::adjEntry chosen = nullptr;
            for (ogdf::adjEntry adj : nodeOf[u]->adjEntries) {
                if (adj->twinNode() == nodeOf[v]) {
                    chosen = adj;
                    break;
                }
            }
            if (chosen == nullptr) {
                message = "missing OGDF adjacency entry while building rotation";
                return false;
            }
            order.push_back(chosen);
        }
        if ((int)order.size() != nodeOf[u]->degree()) {
            message = "rotation length differs from OGDF node degree";
            return false;
        }
        OG.sort(nodeOf[u], order);
    }
    return true;
}

static bool verifyContractionCertificateOgdf(const Graph& original,
                                             const SearchResult& result,
                                             string& message) {
    // Independently replay a successful contraction sequence in OGDF and
    // compare its face, vertex, and edge counts with the custom implementation.
    ogdf::Graph OG;
    vector<ogdf::node> nodeOf;
    if (!buildOgdfGraphWithRotation(original, OG, nodeOf, message)) return false;

    ogdf::CombinatorialEmbedding embedding(OG);
    int originalFaceCount = embedding.numberOfFaces();
    string cycleMessage;
    if (ogdfHasSelfLoopOrParallelEdge(OG, cycleMessage)) {
        message = cycleMessage;
        return false;
    }
    if (originalFaceCount != (int)original.faces().size()) {
        ostringstream os;
        os << "OGDF initial face count " << originalFaceCount
           << " differs from custom face count " << original.faces().size();
        message = os.str();
        return false;
    }

    for (int i = 0; i < (int)result.directedContractions.size(); i++) {
        auto [u, v] = result.directedContractions[i];
        if (u < 0 || u >= (VID)nodeOf.size() || v < 0 || v >= (VID)nodeOf.size() ||
            nodeOf[u] == nullptr || nodeOf[v] == nullptr) {
            ostringstream os;
            os << "OGDF contraction " << (i + 1) << " uses a dead or invalid vertex";
            message = os.str();
            return false;
        }
        ogdf::edge e = findOgdfEdgeBetween(nodeOf, u, v);
        if (e == nullptr) {
            ostringstream os;
            os << "OGDF contraction " << (i + 1) << " does not exist as an edge during replay";
            message = os.str();
            return false;
        }
        if (e->source() != nodeOf[u]) embedding.reverseEdge(e);
        int beforeFaces = embedding.numberOfFaces();
        ogdf::node kept = embedding.contract(e, false);
        if (kept != nodeOf[u]) {
            message = "OGDF contraction kept the wrong endpoint";
            return false;
        }
        nodeOf[v] = nullptr;

        if (embedding.numberOfFaces() != beforeFaces) {
            ostringstream os;
            os << "after OGDF contraction " << (i + 1)
               << ", face count changed from " << beforeFaces
               << " to " << embedding.numberOfFaces();
            message = os.str();
            return false;
        }

        if (ogdfHasSelfLoopOrParallelEdge(OG, cycleMessage)) {
            ostringstream os;
            os << "after OGDF contraction " << (i + 1)
               << ", " << cycleMessage;
            message = os.str();
            return false;
        }
    }

    if (embedding.numberOfFaces() != originalFaceCount) {
        ostringstream os;
        os << "OGDF face count changed from " << originalFaceCount
           << " to " << embedding.numberOfFaces();
        message = os.str();
        return false;
    }

    if (OG.numberOfNodes() != (int)result.finalGraph.aliveVertices().size()) {
        ostringstream os;
        os << "OGDF final node count " << OG.numberOfNodes()
           << " differs from claimed final graph node count "
           << result.finalGraph.aliveVertices().size();
        message = os.str();
        return false;
    }

    if (OG.numberOfEdges() != (int)aliveEdges(result.finalGraph).size()) {
        ostringstream os;
        os << "OGDF final edge count " << OG.numberOfEdges()
           << " differs from claimed final graph edge count "
           << aliveEdges(result.finalGraph).size();
        message = os.str();
        return false;
    }

    for (auto [u, v] : aliveEdges(result.finalGraph)) {
        if (findOgdfEdgeBetween(nodeOf, u, v) == nullptr) {
            ostringstream os;
            os << "OGDF final graph is missing claimed edge "
               << result.finalGraph.name[u] << result.finalGraph.name[v];
            message = os.str();
            return false;
        }
    }

    return true;
}
#endif

static bool allFacesQuadrangles(const Graph& G) {
    // A quadrangulation must have exactly four boundary steps around every face.
    for (const auto& f : G.faces()) {
        if (f.size() != 4) return false;
    }
    return true;
}

// ---------------------------------------------------------------------------
// Turn a partial plane 3-tree into a full plane 3-tree for drawing
// ---------------------------------------------------------------------------

static bool areConsecutiveOnFace(const vector<VID>& face, int i, int j) {
    // Check whether two positions are already joined by a side of this face.
    int n = (int)face.size();
    return (i + 1) % n == j || (j + 1) % n == i;
}

static bool insertAfter(vector<VID>& rot, VID after, VID value) {
    // Insert a neighbor into a clockwise rotation immediately after another one.
    auto it = find(rot.begin(), rot.end(), after);
    if (it == rot.end()) return false;
    rot.insert(it + 1, value);
    return true;
}

static bool insertEdgeInFace(const Graph& G, const vector<VID>& face, int i, int j, Graph& out) {
    // Add a diagonal inside one face and place it in the correct position in
    // both endpoints' clockwise neighbor lists.
    int n = (int)face.size();
    if (n < 4 || i == j || areConsecutiveOnFace(face, i, j)) return false;
    VID a = face[i], b = face[j];
    if (a == b || G.hasEdge(a, b)) return false;

    VID prevA = face[(i - 1 + n) % n];
    VID prevB = face[(j - 1 + n) % n];

    out = G;
    if (!insertAfter(out.adj[a], prevA, b)) return false;
    if (!insertAfter(out.adj[b], prevB, a)) return false;
    return adjacencySymmetric(out);
}

static bool allFacesTriangles(const Graph& G) {
    // A fully triangulated plane graph has three boundary steps around every face.
    for (const auto& f : G.faces()) {
        if (f.size() != 3) return false;
    }
    return true;
}

static bool isPlane3Tree(const Graph& G) {
    // A full plane 3-tree starts from a triangle (or K4) and repeatedly puts a
    // new vertex inside a triangular face, joined to all three corners. Reading
    // this backwards, we repeatedly remove a degree-3 vertex whose neighbors
    // form a triangle.
    vector<VID> verts = G.aliveVertices();
    int n = (int)verts.size();
    if (n < 3) return false;
    if ((int)aliveEdges(G).size() != 3 * n - 6) return false;
    if (!allFacesTriangles(G)) return false;

    vector<set<VID>> adj(G.N);
    vector<bool> alive = G.alive;
    for (VID u : verts) {
        for (VID v : G.adj[u]) if (v >= 0 && v < G.N && G.alive[v]) adj[u].insert(v);
    }

    int remaining = n;
    while (remaining > 4) {
        VID remove = -1;
        for (VID v : verts) {
            if (!alive[v]) continue;
            vector<VID> nb;
            for (VID w : adj[v]) if (alive[w]) nb.push_back(w);
            if ((int)nb.size() != 3) continue;
            if (adj[nb[0]].count(nb[1]) && adj[nb[0]].count(nb[2]) && adj[nb[1]].count(nb[2])) {
                remove = v;
                break;
            }
        }
        if (remove == -1) return false;
        vector<VID> nb;
        for (VID w : adj[remove]) if (alive[w]) nb.push_back(w);
        for (VID w : nb) adj[w].erase(remove);
        adj[remove].clear();
        alive[remove] = false;
        remaining--;
    }

    vector<VID> left;
    for (VID v : verts) if (alive[v]) left.push_back(v);
    if (remaining == 3) {
        return adj[left[0]].count(left[1]) && adj[left[0]].count(left[2]) && adj[left[1]].count(left[2]);
    }
    for (int i = 0; i < 4; i++) {
        for (int j = i + 1; j < 4; j++) {
            if (!adj[left[i]].count(left[j])) return false;
        }
    }
    return true;
}

struct PlaneCompletionResult {
    bool ok = false;
    Graph graph;
    set<pair<VID,VID>> addedEdges;
};

static bool planeCompletionDfs(const Graph& G, set<pair<VID,VID>>& added,
                               unordered_map<string,bool>& dead,
                               PlaneCompletionResult& result,
                               const vector<VID>* preferredBoundary = nullptr,
                               int salt = 0) {
    int n = (int)G.aliveVertices().size();
    int maxEdges = 3 * n - 6;
    int edges = (int)aliveEdges(G).size();
    if (edges > maxEdges) return false;
    if (edges == maxEdges) {
        if (isPlane3Tree(G)) {
            result.ok = true;
            result.graph = G;
            result.addedEdges = added;
            return true;
        }
        return false;
    }

    string key = graphStateKey(G);
    if (dead.count(key)) return false;

    vector<vector<VID>> faces;
    vector<VID> matchedBoundary;
    if (preferredBoundary && findMatchingFace(G, *preferredBoundary, matchedBoundary) &&
        matchedBoundary.size() > 3) {
        faces.push_back(matchedBoundary);
    } else {
        faces = G.faces();
        sort(faces.begin(), faces.end(), [](const vector<VID>& a, const vector<VID>& b) {
            return a.size() > b.size();
        });
    }

    // Split a non-triangular face with a diagonal, then recurse. Trying the
    // alternatives finds a completion compatible with this embedding.
    for (const auto& face : faces) {
        if (face.size() <= 3) continue;
        int m = (int)face.size();
        vector<pair<int,int>> diagonals;
        for (int gap = 2; gap <= m - 2; gap++) {
            for (int i = 0; i < m; i++) {
                int j = (i + gap) % m;
                if (i > j) continue;
                diagonals.push_back({i, j});
            }
        }
        sort(diagonals.begin(), diagonals.end(), [&](pair<int,int> x, pair<int,int> y) {
            VID ax = face[x.first], bx = face[x.second];
            VID ay = face[y.first], by = face[y.second];
            unsigned hx = (unsigned)(ax + 3) * 1103515245u ^
                          (unsigned)(bx + 11) * 2654435761u ^
                          (unsigned)(salt + 17) * 2246822519u;
            unsigned hy = (unsigned)(ay + 3) * 1103515245u ^
                          (unsigned)(by + 11) * 2654435761u ^
                          (unsigned)(salt + 17) * 2246822519u;
            if (salt != 0 && hx != hy) return hx < hy;
            int dx = (int)G.adj[ax].size() + (int)G.adj[bx].size();
            int dy = (int)G.adj[ay].size() + (int)G.adj[by].size();
            if (dx != dy) return dx < dy;
            return edgeKey(ax, bx) < edgeKey(ay, by);
        });
        for (auto [i, j] : diagonals) {
            Graph next;
            if (!insertEdgeInFace(G, face, i, j, next)) continue;
            auto e = edgeKey(face[i], face[j]);
            added.insert(e);
            if (planeCompletionDfs(next, added, dead, result, preferredBoundary, salt)) return true;
            added.erase(e);
        }
        break;
    }

    dead[key] = false;
    return false;
}

static PlaneCompletionResult completeToPlane3TreeByFaceInsertions(
    const Graph& G, const vector<VID>* preferredBoundary = nullptr, int salt = 0) {
    // Try adding noncrossing diagonals until the embedding becomes a plane 3-tree.
    PlaneCompletionResult result;
    set<pair<VID,VID>> added;
    unordered_map<string,bool> dead;
    planeCompletionDfs(G, added, dead, result, preferredBoundary, salt);
    return result;
}

struct Point2D {
    double x = 0.0;
    double y = 0.0;
};

// ---------------------------------------------------------------------------
// Straight-line drawing helpers
//
// Candidate vertex positions are generated, improved for readability, and
// accepted only after checking that edges do not cross and that the clockwise
// neighbor order still matches the input embedding.
// ---------------------------------------------------------------------------

static vector<Point2D> improveInteriorLayout(const Graph& G, vector<Point2D> pos,
                                             const vector<VID>& outer,
                                             const set<pair<VID,VID>>& extraEdges);
static vector<Point2D> balanceFaceDistances(const Graph& G, vector<Point2D> pos,
                                            const vector<VID>& outer,
                                            const set<pair<VID,VID>>& extraEdges);

static double cross2(Point2D a, Point2D b, Point2D c) {
    // Signed area test: indicates which side of directed line a-b contains c.
    return (b.x-a.x)*(c.y-a.y) - (b.y-a.y)*(c.x-a.x);
}

static int orientSign(Point2D a, Point2D b, Point2D c) {
    // Convert the signed-area value into left turn, right turn, or collinear.
    double z = cross2(a,b,c);
    const double EPS = 1e-10;
    if (z > EPS) return 1;
    if (z < -EPS) return -1;
    return 0;
}

static bool onSegment(Point2D a, Point2D b, Point2D p) {
    // Check whether p lies on the finite line segment a-b.
    const double EPS = 1e-10;
    if (fabs(cross2(a,b,p)) > EPS) return false;
    return min(a.x,b.x)-EPS <= p.x && p.x <= max(a.x,b.x)+EPS &&
           min(a.y,b.y)-EPS <= p.y && p.y <= max(a.y,b.y)+EPS;
}

static bool segmentsIntersect(Point2D a, Point2D b, Point2D c, Point2D d) {
    // Detect proper crossings as well as endpoints lying on the other segment.
    int o1 = orientSign(a,b,c), o2 = orientSign(a,b,d);
    int o3 = orientSign(c,d,a), o4 = orientSign(c,d,b);
    if (o1 != o2 && o3 != o4) return true;
    if (o1 == 0 && onSegment(a,b,c)) return true;
    if (o2 == 0 && onSegment(a,b,d)) return true;
    if (o3 == 0 && onSegment(c,d,a)) return true;
    if (o4 == 0 && onSegment(c,d,b)) return true;
    return false;
}

static double dist2(Point2D a, Point2D b) {
    // Squared distance avoids an unnecessary square root when only comparing distances.
    double dx = a.x - b.x, dy = a.y - b.y;
    return dx*dx + dy*dy;
}

static bool incidentEdgesOverlap(Point2D shared, Point2D a, Point2D b) {
    // Detect two edges leaving their shared vertex in almost the same direction.
    double la = sqrt(dist2(shared, a));
    double lb = sqrt(dist2(shared, b));
    if (la < 1e-12 || lb < 1e-12) return true;
    double cross = fabs(cross2(shared, a, b));
    double dot = (a.x - shared.x) * (b.x - shared.x) +
                 (a.y - shared.y) * (b.y - shared.y);
    double sinAngle = cross / (la * lb);
    return dot > 0.0 && sinAngle < 1e-5;
}

static void makeDir(const string& dir) {
    // Ensure an output directory exists before writing an SVG file.
    string cmd = "mkdir -p \"" + dir + "\"";
    system(cmd.c_str());
}

static void clearDrawingDirectory() {
    // Remove drawings from an earlier run and recreate the output directory.
    const string root = "partial3tree_drawings";
    error_code ec;
    if (fs::exists(root, ec)) {
        for (const auto& entry : fs::directory_iterator(root, ec)) {
            fs::remove_all(entry.path(), ec);
        }
    }
    fs::create_directories(root, ec);
}

static string graphDirName(int index) {
    // Give each input graph a predictable directory such as graph_003.
    ostringstream os;
    os << "partial3tree_drawings/graph_" << setw(3) << setfill('0') << index;
    return os.str();
}

static vector<Point2D> computeCircularLayout(const Graph& G) {
    // Simple fallback that places every active vertex evenly around a circle.
    const double PI = acos(-1.0);
    vector<Point2D> pos(G.N);
    vector<VID> verts = G.aliveVertices();
    int n = (int)verts.size();
    double R = max(1.0, (double)n);
    for (int i = 0; i < n; i++) {
        double a = 2.0 * PI * i / max(1, n) - PI / 2.0;
        pos[verts[i]] = {R * cos(a), R * sin(a)};
    }
    return pos;
}

static vector<pair<VID,VID>> drawingEdges(const Graph& G, const set<pair<VID,VID>>& extraEdges) {
    // Combine real and temporary completion edges without duplicates.
    vector<pair<VID,VID>> edges = aliveEdges(G);
    set<pair<VID,VID>> seen(edges.begin(), edges.end());
    for (auto e : extraEdges) {
        VID u = e.first, v = e.second;
        if (u < 0 || u >= G.N || v < 0 || v >= G.N || !G.alive[u] || !G.alive[v]) continue;
        auto k = edgeKey(u, v);
        if (seen.insert(k).second) edges.push_back(k);
    }
    return edges;
}

static bool drawingHasNoCrossings(const Graph& G, const vector<Point2D>& pos,
                                  const set<pair<VID,VID>>& extraEdges = {}) {
    // Verify that nonincident edges do not cross and incident edges do not overlap.
    auto edges = drawingEdges(G, extraEdges);
    for (int i = 0; i < (int)edges.size(); i++) {
        auto [a,b] = edges[i];
        for (int j = i + 1; j < (int)edges.size(); j++) {
            auto [c,d] = edges[j];
            if (a == c) {
                if (incidentEdgesOverlap(pos[a], pos[b], pos[d])) return false;
                continue;
            }
            if (a == d) {
                if (incidentEdgesOverlap(pos[a], pos[b], pos[c])) return false;
                continue;
            }
            if (b == c) {
                if (incidentEdgesOverlap(pos[b], pos[a], pos[d])) return false;
                continue;
            }
            if (b == d) {
                if (incidentEdgesOverlap(pos[b], pos[a], pos[c])) return false;
                continue;
            }
            if (segmentsIntersect(pos[a], pos[b], pos[c], pos[d])) return false;
        }
    }
    return true;
}

static bool sameCyclicOrder(const vector<VID>& a, const vector<VID>& b, bool allowReverse = true) {
    // Compare circular sequences while ignoring their starting position and,
    // optionally, the direction in which the circle was read.
    int n = (int)a.size();
    if ((int)b.size() != n) return false;
    if (n <= 1) return true;
    for (int shift = 0; shift < n; shift++) {
        bool ok = true;
        for (int i = 0; i < n; i++) {
            if (a[i] != b[(shift + i) % n]) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
        if (!allowReverse) continue;
        ok = true;
        for (int i = 0; i < n; i++) {
            if (a[i] != b[(shift - i + n) % n]) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
    }
    return false;
}

static bool drawingPreservesRotation(const Graph& G, const vector<Point2D>& pos) {
    // Sort neighbors by their geometric angle and compare that circular order
    // with the clockwise order stored in the graph.
    for (VID u : G.aliveVertices()) {
        vector<VID> expected;
        for (VID v : G.adj[u]) {
            if (v >= 0 && v < G.N && G.alive[v]) expected.push_back(v);
        }
        if (expected.size() <= 2) continue;

        vector<pair<double,VID>> byAngle;
        for (VID v : expected) {
            double angle = atan2(pos[v].y - pos[u].y, pos[v].x - pos[u].x);
            byAngle.push_back({angle, v});
        }
        sort(byAngle.begin(), byAngle.end());
        vector<VID> geometric;
        for (auto [angle, v] : byAngle) geometric.push_back(v);

        if (!sameCyclicOrder(expected, geometric)) return false;
    }
    return true;
}

static bool drawingIsVerified(const Graph& G, const vector<Point2D>& pos,
                              const set<pair<VID,VID>>& extraEdges = {}) {
    // Final validity check for generated coordinates.
    return drawingHasNoCrossings(G, pos, extraEdges) &&
           extraEdges.empty() &&
           drawingPreservesRotation(G, pos);
}

static double distancePointSegment(Point2D p, Point2D a, Point2D b) {
    // Shortest Euclidean distance from p to any point on segment a-b.
    double len2 = dist2(a, b);
    if (len2 < 1e-18) return sqrt(dist2(p, a));
    double t = ((p.x - a.x) * (b.x - a.x) + (p.y - a.y) * (b.y - a.y)) / len2;
    t = max(0.0, min(1.0, t));
    Point2D q{a.x + t * (b.x - a.x), a.y + t * (b.y - a.y)};
    return sqrt(dist2(p, q));
}

static Point2D closestPointOnSegment(Point2D p, Point2D a, Point2D b) {
    // Return the actual point on a-b that is closest to p.
    double len2 = dist2(a, b);
    if (len2 < 1e-18) return a;
    double t = ((p.x - a.x) * (b.x - a.x) + (p.y - a.y) * (b.y - a.y)) / len2;
    t = max(0.0, min(1.0, t));
    return {a.x + t * (b.x - a.x), a.y + t * (b.y - a.y)};
}

static double distanceSegmentSegment(Point2D a, Point2D b, Point2D c, Point2D d) {
    // Shortest distance between two finite segments; zero if they intersect.
    if (segmentsIntersect(a, b, c, d)) return 0.0;
    return min(min(distancePointSegment(a, c, d), distancePointSegment(b, c, d)),
               min(distancePointSegment(c, a, b), distancePointSegment(d, a, b)));
}

static double minNonincidentEdgeDistance(const Graph& G, const vector<Point2D>& pos,
                                         const set<pair<VID,VID>>& extraEdges = {}) {
    // Measure the smallest visual gap between edges that share no endpoint.
    auto edges = drawingEdges(G, extraEdges);
    double best = 1e100;
    for (int i = 0; i < (int)edges.size(); i++) {
        auto [a, b] = edges[i];
        for (int j = i + 1; j < (int)edges.size(); j++) {
            auto [c, d] = edges[j];
            if (a == c || a == d || b == c || b == d) continue;
            best = min(best, distanceSegmentSegment(pos[a], pos[b], pos[c], pos[d]));
        }
    }
    return best == 1e100 ? 1.0 : best;
}

static vector<Point2D> normalizedLayout(const Graph& G, const vector<Point2D>& pos) {
    // Translate and uniformly scale coordinates into a comparable unit box.
    vector<Point2D> out = pos;
    vector<VID> verts = G.aliveVertices();
    double minx = 1e100, maxx = -1e100, miny = 1e100, maxy = -1e100;
    for (VID v : verts) {
        minx = min(minx, pos[v].x); maxx = max(maxx, pos[v].x);
        miny = min(miny, pos[v].y); maxy = max(maxy, pos[v].y);
    }
    double span = max(maxx - minx, maxy - miny);
    if (span < 1e-12) span = 1.0;
    for (VID v : verts) {
        out[v] = {(pos[v].x - minx) / span, (pos[v].y - miny) / span};
    }
    return out;
}

static bool edgeOnBoundary(pair<VID,VID> e, const vector<VID>* outer) {
    // Check whether an edge is a side of the selected outer face.
    if (!outer || outer->size() < 2) return false;
    int n = (int)outer->size();
    for (int i = 0; i < n; i++) {
        if (edgeKey((*outer)[i], (*outer)[(i + 1) % n]) == e) return true;
    }
    return false;
}

static double layoutQuality(const Graph& G, const vector<Point2D>& pos,
                            const set<pair<VID,VID>>& extraEdges = {},
                            const vector<VID>* outer = nullptr) {
    // Larger scores favor separated vertices/edges and discourage needlessly
    // long interior edges. This affects appearance, never recognition.
    vector<VID> verts = G.aliveVertices();
    vector<Point2D> p = normalizedLayout(G, pos);
    auto edges = drawingEdges(G, extraEdges);

    double minVertexDist = 1e100;
    for (int i = 0; i < (int)verts.size(); i++) {
        for (int j = i + 1; j < (int)verts.size(); j++) {
            minVertexDist = min(minVertexDist, sqrt(dist2(p[verts[i]], p[verts[j]])));
        }
    }

    double minVertexEdgeDist = 1e100;
    for (VID v : verts) {
        for (auto [a, b] : edges) {
            if (v == a || v == b) continue;
            minVertexEdgeDist = min(minVertexEdgeDist, distancePointSegment(p[v], p[a], p[b]));
        }
    }

    double minEdgeEdgeDist = 1e100;
    for (int i = 0; i < (int)edges.size(); i++) {
        auto [a, b] = edges[i];
        for (int j = i + 1; j < (int)edges.size(); j++) {
            auto [c, d] = edges[j];
            if (a == c || a == d || b == c || b == d) continue;
            minEdgeEdgeDist = min(minEdgeEdgeDist, distanceSegmentSegment(p[a], p[b], p[c], p[d]));
        }
    }

    if (minVertexDist == 1e100) minVertexDist = 1.0;
    if (minVertexEdgeDist == 1e100) minVertexEdgeDist = 1.0;
    if (minEdgeEdgeDist == 1e100) minEdgeEdgeDist = 1.0;

    double minFaceArea = 1e100;
    double faceAreaSum = 0.0;
    int faceAreaCount = 0;
    for (const auto& face : G.faces()) {
        if (face.size() < 3) continue;
        double area2 = 0.0;
        for (int i = 0; i < (int)face.size(); i++) {
            Point2D a = p[face[i]];
            Point2D b = p[face[(i + 1) % face.size()]];
            area2 += a.x * b.y - a.y * b.x;
        }
        double area = 0.5 * fabs(area2);
        minFaceArea = min(minFaceArea, area);
        faceAreaSum += min(0.08, area);
        faceAreaCount++;
    }
    if (minFaceArea == 1e100) minFaceArea = 1.0;

    double score = 0.0;
    score += 3.00 * minVertexDist;
    score += 1.75 * minVertexEdgeDist;
    score += 1000.00 * minEdgeEdgeDist;
    score += 30.00 * sqrt(max(0.0, minEdgeEdgeDist));
    score += 6.00 * sqrt(max(0.0, minFaceArea));
    if (faceAreaCount) score += 1.25 * faceAreaSum / faceAreaCount;

    // Reward the whole distribution too, so the optimizer does not improve one
    // closest pair while leaving many nearly parallel edges visually glued.
    double edgeEdgeSum = 0.0;
    int edgeEdgeCount = 0;
    for (int i = 0; i < (int)edges.size(); i++) {
        auto [a, b] = edges[i];
        for (int j = i + 1; j < (int)edges.size(); j++) {
            auto [c, d] = edges[j];
            if (a == c || a == d || b == c || b == d) continue;
            edgeEdgeSum += min(0.20, distanceSegmentSegment(p[a], p[b], p[c], p[d]));
            edgeEdgeCount++;
        }
    }
    if (edgeEdgeCount) score += 0.55 * edgeEdgeSum / edgeEdgeCount;

    double innerLengthSum = 0.0, innerLengthMax = 0.0;
    int innerLengthCount = 0;
    for (auto e : edges) {
        if (edgeOnBoundary(e, outer)) continue;
        double len = sqrt(dist2(p[e.first], p[e.second]));
        innerLengthSum += min(1.0, len);
        innerLengthMax = max(innerLengthMax, min(1.0, len));
        innerLengthCount++;
    }
    if (innerLengthCount && minEdgeEdgeDist > 0.025 && minVertexEdgeDist > 0.025) {
        double avgInnerLength = innerLengthSum / innerLengthCount;
        score -= 0.38 * avgInnerLength;
        score -= 0.22 * innerLengthMax;
    }
    return score;
}

static bool sameCyclicFace(const vector<VID>& a, const vector<VID>& b) {
    // Compare two face boundaries up to rotation and reversal.
    int n = (int)a.size();
    if ((int)b.size() != n) return false;
    for (int shift = 0; shift < n; shift++) {
        bool ok = true;
        for (int i = 0; i < n; i++) {
            if (a[i] != b[(shift + i) % n]) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
        ok = true;
        for (int i = 0; i < n; i++) {
            if (a[i] != b[(shift - i + n) % n]) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
    }
    return false;
}

static bool findMatchingFace(const Graph& G, const vector<VID>& preferred, vector<VID>& matched) {
    // Find the graph's stored version of a requested cyclic face boundary.
    if (preferred.empty()) return false;
    for (VID v : preferred) {
        if (v < 0 || v >= G.N || !G.alive[v]) return false;
    }
    for (const auto& face : G.faces()) {
        if (sameCyclicFace(face, preferred)) {
            matched = face;
            return true;
        }
    }
    return false;
}

static bool validDrawableBoundary(const Graph& G, const vector<VID>& boundary,
                                  const set<pair<VID,VID>>& extraEdges = {}) {
    // Ensure an outer polygon uses distinct active vertices and existing sides.
    if (boundary.size() < 3) return false;
    set<VID> seen;
    for (VID v : boundary) {
        if (v < 0 || v >= G.N || !G.alive[v]) return false;
        if (!seen.insert(v).second) return false;
    }
    int n = (int)boundary.size();
    for (int i = 0; i < n; i++) {
        VID a = boundary[i], b = boundary[(i + 1) % n];
        if (!G.hasEdge(a, b) && !extraEdges.count(edgeKey(a, b))) return false;
    }
    return true;
}

static double baryWeight(VID u, VID w, int mode) {
    // Generate a deterministic positive weight for layout experimentation.
    // Mode zero gives the standard equal-weight Tutte layout.
    if (mode == 0) return 1.0;
    unsigned x = (unsigned)(u + 1) * 1103515245u
               ^ (unsigned)(w + 7) * 2654435761u
               ^ (unsigned)(mode + 13) * 2246822519u;
    x ^= x >> 13;
    x *= 1274126177u;
    x ^= x >> 16;
    double bucket = (double)(x % 4096) / 4095.0;
    double spread = 0.45 + 0.025 * (mode % 96);
    double exponent = -spread + 2.0 * spread * bucket;
    return exp(exponent);
}

static vector<Point2D> solveTutteLayoutForOuterFace(const Graph& G, const vector<VID>& outer,
                                                    int weightMode = 0) {
    // Fix the chosen outer face on a circle. Each interior vertex is repeatedly
    // moved to a weighted average of its neighbors; for a suitable planar graph
    // this produces a straight-line drawing without crossings.
    const double PI = acos(-1.0);
    vector<Point2D> pos(G.N);
    vector<bool> fixed(G.N, false);
    vector<VID> verts = G.aliveVertices();

    int m = (int)outer.size();
    double R = max(3.0, (double)verts.size());
    for (int i = 0; i < m; i++) {
        double a = 2.0 * PI * i / max(1, m) - PI/2.0;
        VID v = outer[i];
        if (v < 0 || v >= G.N || !G.alive[v]) continue;
        pos[v] = {R*cos(a), R*sin(a)};
        fixed[v] = true;
    }

    vector<VID> vars;
    vector<int> varIndex(G.N, -1);
    for (VID v : verts) {
        if (!fixed[v]) {
            varIndex[v] = (int)vars.size();
            vars.push_back(v);
        }
    }

    int n = (int)vars.size();
    if (n == 0) return pos;

    vector<vector<double>> A(n, vector<double>(n, 0.0));
    vector<double> bx(n, 0.0), by(n, 0.0);
    for (int row = 0; row < n; row++) {
        VID u = vars[row];
        A[row][row] = 1.0;
        double totalWeight = 0.0;
        for (VID w : G.adj[u]) {
            if (w >= 0 && w < G.N && G.alive[w]) totalWeight += baryWeight(u, w, weightMode);
        }
        if (totalWeight <= 0.0) continue;
        for (VID w : G.adj[u]) {
            if (w < 0 || w >= G.N || !G.alive[w]) continue;
            double coeff = baryWeight(u, w, weightMode) / totalWeight;
            if (fixed[w]) {
                bx[row] += coeff * pos[w].x;
                by[row] += coeff * pos[w].y;
            } else if (varIndex[w] != -1) {
                A[row][varIndex[w]] -= coeff;
            }
        }
    }

    auto solve = [&](vector<double> b) {
        vector<vector<double>> M = A;
        const double EPS = 1e-10;
        for (int col = 0; col < n; col++) {
            int pivot = col;
            for (int r = col + 1; r < n; r++) {
                if (fabs(M[r][col]) > fabs(M[pivot][col])) pivot = r;
            }
            if (fabs(M[pivot][col]) < EPS) continue;
            swap(M[pivot], M[col]);
            swap(b[pivot], b[col]);
            double div = M[col][col];
            for (int c = col; c < n; c++) M[col][c] /= div;
            b[col] /= div;
            for (int r = 0; r < n; r++) {
                if (r == col) continue;
                double factor = M[r][col];
                if (fabs(factor) < EPS) continue;
                for (int c = col; c < n; c++) M[r][c] -= factor * M[col][c];
                b[r] -= factor * b[col];
            }
        }
        return b;
    };

    vector<double> xs = solve(bx), ys = solve(by);
    for (int i = 0; i < n; i++) pos[vars[i]] = {xs[i], ys[i]};
    return pos;
}

static bool pointInPolygon(Point2D p, const vector<Point2D>& poly) {
    // Use ray casting to test whether a point lies inside a polygon.
    bool inside = false;
    int n = (int)poly.size();
    for (int i = 0, j = n - 1; i < n; j = i++) {
        bool crosses = ((poly[i].y > p.y) != (poly[j].y > p.y)) &&
                       (p.x < (poly[j].x - poly[i].x) * (p.y - poly[i].y) /
                                  (poly[j].y - poly[i].y + 1e-30) + poly[i].x);
        if (crosses) inside = !inside;
    }
    return inside;
}

struct FaceDistanceSample {
    // One vertex-to-opposite-edge measurement used to improve face readability.
    VID v = -1;
    VID a = -1;
    VID b = -1;
    double d = 0.0;
};

static double faceDistanceImbalance(const Graph& G, const vector<Point2D>& pos) {
    // Score how unevenly vertices sit relative to the opposite sides of their faces.
    double score = 0.0;
    for (const auto& face : G.faces()) {
        int n = (int)face.size();
        if (n < 3) continue;
        vector<double> distances;
        for (int i = 0; i < n; i++) {
            VID v = face[i];
            for (int j = 0; j < n; j++) {
                VID a = face[j], b = face[(j + 1) % n];
                if (v == a || v == b) continue;
                distances.push_back(distancePointSegment(pos[v], pos[a], pos[b]));
            }
        }
        if (distances.empty()) continue;
        double avg = 0.0;
        for (double d : distances) avg += d;
        avg /= distances.size();
        if (avg < 1e-12) continue;
        for (double d : distances) {
            double excess = max(0.0, d / avg - 1.25);
            score += excess * excess;
        }
    }
    return score;
}

static vector<FaceDistanceSample> faceDistanceSamples(const Graph& G, const vector<Point2D>& pos) {
    // Collect the local measurements used by the face-balancing pass.
    vector<FaceDistanceSample> out;
    for (const auto& face : G.faces()) {
        int n = (int)face.size();
        if (n < 3) continue;
        vector<FaceDistanceSample> local;
        double sum = 0.0;
        for (int i = 0; i < n; i++) {
            VID v = face[i];
            for (int j = 0; j < n; j++) {
                VID a = face[j], b = face[(j + 1) % n];
                if (v == a || v == b) continue;
                double d = distancePointSegment(pos[v], pos[a], pos[b]);
                local.push_back({v, a, b, d});
                sum += d;
            }
        }
        if (local.empty()) continue;
        double avg = sum / local.size();
        for (auto s : local) {
            if (avg > 1e-12 && s.d > 1.35 * avg) out.push_back(s);
        }
    }
    sort(out.begin(), out.end(), [](const FaceDistanceSample& x, const FaceDistanceSample& y) {
        return x.d > y.d;
    });
    return out;
}

static vector<Point2D> balanceFaceDistances(const Graph& G, vector<Point2D> pos,
                                            const vector<VID>& outer,
                                            const set<pair<VID,VID>>& extraEdges = {}) {
    // Nudge interior vertices toward more even face spacing without breaking validity.
    if (outer.size() < 3) return pos;

    vector<bool> fixed(G.N, false);
    vector<Point2D> outerPoly;
    for (VID v : outer) {
        if (v >= 0 && v < G.N && G.alive[v]) {
            fixed[v] = true;
            outerPoly.push_back(pos[v]);
        }
    }
    if (outerPoly.size() < 3) return pos;

    double bestImbalance = faceDistanceImbalance(G, pos);
    double bestQuality = layoutQuality(G, pos, extraEdges, &outer);
    double bestEdgeClearance = minNonincidentEdgeDistance(G, pos, extraEdges);
    vector<double> fractions = {0.08, 0.14, 0.22, 0.32};

    for (int round = 0; round < 10; round++) {
        bool changed = false;
        vector<FaceDistanceSample> samples = faceDistanceSamples(G, pos);
        for (const auto& sample : samples) {
            VID v = sample.v;
            if (v < 0 || v >= G.N || fixed[v] || !G.alive[v]) continue;
            Point2D target = closestPointOnSegment(pos[v], pos[sample.a], pos[sample.b]);
            for (double frac : fractions) {
                vector<Point2D> trial = pos;
                trial[v] = {
                    pos[v].x + frac * (target.x - pos[v].x),
                    pos[v].y + frac * (target.y - pos[v].y)
                };
                if (!pointInPolygon(trial[v], outerPoly)) continue;
                if (!drawingIsVerified(G, trial, extraEdges)) continue;
                double edgeClearance = minNonincidentEdgeDistance(G, trial, extraEdges);
                if (edgeClearance + 1e-9 < bestEdgeClearance) continue;
                double imbalance = faceDistanceImbalance(G, trial);
                double quality = layoutQuality(G, trial, extraEdges, &outer);
                if (imbalance < bestImbalance - 1e-8 && quality + 0.015 >= bestQuality) {
                    pos.swap(trial);
                    bestImbalance = imbalance;
                    bestQuality = max(bestQuality, quality);
                    bestEdgeClearance = edgeClearance;
                    changed = true;
                    break;
                }
            }
        }
        if (!changed) break;
    }
    return pos;
}

static vector<Point2D> improveEdgeClearance(const Graph& G, vector<Point2D> pos,
                                            const vector<VID>& outer,
                                            const set<pair<VID,VID>>& extraEdges = {}) {
    // Nudge interior vertices to increase the gap between unrelated edges.
    if (outer.size() < 3) return pos;

    vector<bool> fixed(G.N, false);
    vector<Point2D> outerPoly;
    for (VID v : outer) {
        if (v >= 0 && v < G.N && G.alive[v]) {
            fixed[v] = true;
            outerPoly.push_back(pos[v]);
        }
    }
    if (outerPoly.size() < 3) return pos;

    vector<VID> verts = G.aliveVertices();
    double minx = 1e100, maxx = -1e100, miny = 1e100, maxy = -1e100;
    for (VID v : verts) {
        minx = min(minx, pos[v].x); maxx = max(maxx, pos[v].x);
        miny = min(miny, pos[v].y); maxy = max(maxy, pos[v].y);
    }
    double span = max(maxx - minx, maxy - miny);
    if (span < 1e-9) span = 1.0;

    vector<Point2D> dirs = {
        {1,0}, {-1,0}, {0,1}, {0,-1},
        {0.707,0.707}, {-0.707,0.707}, {0.707,-0.707}, {-0.707,-0.707},
        {0.923,0.382}, {-0.923,0.382}, {0.923,-0.382}, {-0.923,-0.382},
        {0.382,0.923}, {-0.382,0.923}, {0.382,-0.923}, {-0.382,-0.923}
    };

    double bestClearance = minNonincidentEdgeDistance(G, pos, extraEdges);
    double bestQuality = layoutQuality(G, pos, extraEdges, &outer);
    for (int round = 0; round < 44; round++) {
        double step = span * 0.050 * pow(0.90, round);
        bool changed = false;
        for (VID v : verts) {
            if (fixed[v]) continue;
            Point2D old = pos[v];
            for (Point2D d : dirs) {
                vector<Point2D> trial = pos;
                trial[v] = {old.x + step * d.x, old.y + step * d.y};
                if (!pointInPolygon(trial[v], outerPoly)) continue;
                if (!drawingIsVerified(G, trial, extraEdges)) continue;
                double clearance = minNonincidentEdgeDistance(G, trial, extraEdges);
                if (clearance <= bestClearance + 1e-9) continue;
                double quality = layoutQuality(G, trial, extraEdges, &outer);
                pos.swap(trial);
                old = pos[v];
                bestClearance = clearance;
                bestQuality = max(bestQuality, quality);
                changed = true;
            }
        }
        if (!changed && round > 14) break;
    }
    return pos;
}

struct ThreeTreeInsertStep {
    // Records a removable vertex and the triangle that surrounded it.
    VID v = -1;
    array<VID,3> parent{};
};

struct TriangleSubdivisionNode {
    // A node in the history of repeatedly splitting one triangle into three.
    array<VID,3> tri{};
    VID inserted = -1;
    array<int,3> child{{-1, -1, -1}};
    int weight = 1;
};

static string triangleSetKey(array<VID,3> tri) {
    // Identify a triangle independently of the order of its three corners.
    vector<VID> v = {tri[0], tri[1], tri[2]};
    sort(v.begin(), v.end());
    return to_string(v[0]) + "," + to_string(v[1]) + "," + to_string(v[2]);
}

static bool plane3TreeDeconstructionKeepingOuter(const Graph& G, const vector<VID>& outer,
                                                 vector<ThreeTreeInsertStep>& steps,
                                                 int salt = 0) {
    if (outer.size() != 3 || !isPlane3Tree(G)) return false;
    set<VID> outerSet(outer.begin(), outer.end());
    if ((int)outerSet.size() != 3) return false;

    vector<set<VID>> adj(G.N);
    vector<bool> alive = G.alive;
    vector<VID> verts = G.aliveVertices();
    for (VID u : verts) {
        for (VID v : G.adj[u]) {
            if (v >= 0 && v < G.N && G.alive[v]) adj[u].insert(v);
        }
    }

    int remaining = (int)verts.size();
    steps.clear();
    // Remove the last-added vertex repeatedly while preserving the requested
    // outer triangle. Reversing these steps reconstructs the 3-tree.
    while (remaining > 3) {
        vector<ThreeTreeInsertStep> candidates;
        for (VID v : verts) {
            if (!alive[v] || outerSet.count(v)) continue;
            vector<VID> nb;
            for (VID w : adj[v]) if (alive[w]) nb.push_back(w);
            if ((int)nb.size() != 3) continue;
            if (adj[nb[0]].count(nb[1]) && adj[nb[0]].count(nb[2]) && adj[nb[1]].count(nb[2])) {
                candidates.push_back({v, {nb[0], nb[1], nb[2]}});
            }
        }
        if (candidates.empty()) return false;
        sort(candidates.begin(), candidates.end(), [&](const ThreeTreeInsertStep& a,
                                                       const ThreeTreeInsertStep& b) {
            if (salt == 0) return a.v < b.v;
            unsigned ha = (unsigned)(a.v + 5) * 1103515245u ^
                          (unsigned)(salt + 19) * 2654435761u;
            unsigned hb = (unsigned)(b.v + 5) * 1103515245u ^
                          (unsigned)(salt + 19) * 2654435761u;
            if (ha != hb) return ha < hb;
            return a.v < b.v;
        });
        VID remove = candidates.front().v;
        array<VID,3> parent = candidates.front().parent;
        steps.push_back({remove, parent});
        for (VID w : parent) adj[w].erase(remove);
        adj[remove].clear();
        alive[remove] = false;
        remaining--;
    }

    for (VID v : verts) {
        if (alive[v] != (outerSet.count(v) > 0)) return false;
    }
    return true;
}

static int computeSubdivisionWeights(vector<TriangleSubdivisionNode>& nodes, int id) {
    // Count how much nested triangle content belongs below each subdivision node.
    bool leaf = true;
    int total = 0;
    for (int c : nodes[id].child) {
        if (c != -1) {
            leaf = false;
            total += computeSubdivisionWeights(nodes, c);
        }
    }
    nodes[id].weight = leaf ? 1 : total;
    return nodes[id].weight;
}

static bool buildTriangleSubdivisionTree(const vector<ThreeTreeInsertStep>& deconstructionSteps,
                                         const vector<VID>& outer,
                                         vector<TriangleSubdivisionNode>& nodes) {
    // Reverse the removal history into a tree describing which triangle each
    // vertex was inserted into and the three smaller triangles it created.
    nodes.clear();
    nodes.push_back({{outer[0], outer[1], outer[2]}, -1, {{-1, -1, -1}}, 1});
    vector<ThreeTreeInsertStep> steps = deconstructionSteps;
    reverse(steps.begin(), steps.end());
    for (const auto& step : steps) {
        string key = triangleSetKey(step.parent);
        int parentId = -1;
        for (int i = 0; i < (int)nodes.size(); i++) {
            if (nodes[i].inserted != -1) continue;
            if (triangleSetKey(nodes[i].tri) == key) {
                parentId = i;
                break;
            }
        }
        if (parentId == -1) return false;
        auto tri = nodes[parentId].tri;
        nodes[parentId].inserted = step.v;
        nodes[parentId].child[0] = (int)nodes.size();
        nodes.push_back({{step.v, tri[1], tri[2]}, -1, {{-1, -1, -1}}, 1});
        nodes[parentId].child[1] = (int)nodes.size();
        nodes.push_back({{tri[0], step.v, tri[2]}, -1, {{-1, -1, -1}}, 1});
        nodes[parentId].child[2] = (int)nodes.size();
        nodes.push_back({{tri[0], tri[1], step.v}, -1, {{-1, -1, -1}}, 1});
    }
    computeSubdivisionWeights(nodes, 0);
    return true;
}

static void assignAreaSubdivisionCoordinates(const vector<TriangleSubdivisionNode>& nodes,
                                             int id,
                                             vector<Point2D>& pos,
                                             vector<bool>& placed) {
    // Place each inserted vertex inside its parent triangle, allocating more
    // space toward child triangles that contain more descendants.
    const auto& node = nodes[id];
    if (node.inserted == -1) return;
    int total = 0;
    for (int c : node.child) total += nodes[c].weight;
    if (total <= 0) return;
    double a = (double)nodes[node.child[0]].weight / total;
    double b = (double)nodes[node.child[1]].weight / total;
    double c = (double)nodes[node.child[2]].weight / total;
    VID A = node.tri[0], B = node.tri[1], C = node.tri[2];
    pos[node.inserted] = {
        a * pos[A].x + b * pos[B].x + c * pos[C].x,
        a * pos[A].y + b * pos[B].y + c * pos[C].y
    };
    placed[node.inserted] = true;
    for (int child : node.child) assignAreaSubdivisionCoordinates(nodes, child, pos, placed);
}

static bool constructAreaPlane3TreeLayout(const Graph& G, const vector<VID>& outer,
                                          vector<Point2D>& out,
                                          int salt = 0) {
    // Build a plane-3-tree drawing directly from its triangle insertion history.
    vector<ThreeTreeInsertStep> steps;
    if (!plane3TreeDeconstructionKeepingOuter(G, outer, steps, salt)) return false;
    vector<TriangleSubdivisionNode> nodes;
    if (!buildTriangleSubdivisionTree(steps, outer, nodes)) return false;

    const double PI = acos(-1.0);
    vector<Point2D> pos(G.N);
    vector<bool> placed(G.N, false);
    vector<VID> verts = G.aliveVertices();
    double R = max(3.0, (double)verts.size());
    for (int i = 0; i < 3; i++) {
        double a = 2.0 * PI * i / 3.0 - PI / 2.0;
        pos[outer[i]] = {R * cos(a), R * sin(a)};
        placed[outer[i]] = true;
    }

    assignAreaSubdivisionCoordinates(nodes, 0, pos, placed);
    for (VID v : verts) {
        if (!placed[v]) return false;
    }

    if (!drawingIsVerified(G, pos)) return false;
    pos = improveInteriorLayout(G, pos, outer, {});
    pos = balanceFaceDistances(G, pos, outer, {});
    pos = improveEdgeClearance(G, pos, outer, {});
    if (!drawingIsVerified(G, pos)) return false;
    out = pos;
    return true;
}

static vector<Point2D> improveInteriorLayout(const Graph& G, vector<Point2D> pos,
                                             const vector<VID>& outer,
                                             const set<pair<VID,VID>>& extraEdges = {}) {
    // Try small moves of non-boundary vertices and keep moves that improve the
    // overall readability score without introducing a crossing.
    if (outer.size() < 3) return pos;

    vector<bool> fixed(G.N, false);
    vector<Point2D> outerPoly;
    for (VID v : outer) {
        if (v >= 0 && v < G.N && G.alive[v]) {
            fixed[v] = true;
            outerPoly.push_back(pos[v]);
        }
    }
    if (outerPoly.size() < 3) return pos;

    vector<VID> verts = G.aliveVertices();
    double minx = 1e100, maxx = -1e100, miny = 1e100, maxy = -1e100;
    for (VID v : verts) {
        minx = min(minx, pos[v].x); maxx = max(maxx, pos[v].x);
        miny = min(miny, pos[v].y); maxy = max(maxy, pos[v].y);
    }
    double span = max(maxx - minx, maxy - miny);
    if (span < 1e-9) span = 1.0;

    vector<Point2D> dirs = {
        {1,0}, {-1,0}, {0,1}, {0,-1},
        {0.707,0.707}, {-0.707,0.707}, {0.707,-0.707}, {-0.707,-0.707}
    };

    double best = layoutQuality(G, pos, extraEdges, &outer);
    for (int round = 0; round < 36; round++) {
        double step = span * 0.075 * pow(0.88, round);
        bool changed = false;
        for (VID v : verts) {
            if (fixed[v]) continue;
            Point2D old = pos[v];
            for (Point2D d : dirs) {
                vector<Point2D> trial = pos;
                trial[v] = {old.x + step * d.x, old.y + step * d.y};
                if (!pointInPolygon(trial[v], outerPoly)) continue;
                if (!drawingIsVerified(G, trial, extraEdges)) continue;
                double score = layoutQuality(G, trial, extraEdges, &outer);
                if (score > best + 1e-10) {
                    pos.swap(trial);
                    best = score;
                    changed = true;
                    old = pos[v];
                }
            }
        }
        if (!changed && round > 10) break;
    }
    return pos;
}

static unsigned layoutRand(unsigned& state) {
    // Small deterministic pseudo-random generator used by the layout fallback.
    state = state * 1664525u + 1013904223u;
    return state;
}

static bool randomInteriorLayout(const Graph& G, const vector<VID>& outer,
                                 vector<Point2D>& out,
                                 const set<pair<VID,VID>>& extraEdges = {}) {
    // Last-resort layout search: randomly place interior vertices and retain
    // only verified crossing-free candidates.
    if (outer.size() < 3) return false;
    const double PI = acos(-1.0);
    vector<VID> verts = G.aliveVertices();
    vector<bool> fixed(G.N, false);
    vector<Point2D> poly;
    vector<Point2D> base(G.N);

    int m = (int)outer.size();
    double R = max(3.0, (double)verts.size());
    for (int i = 0; i < m; i++) {
        VID v = outer[i];
        if (v < 0 || v >= G.N || !G.alive[v]) return false;
        double a = 2.0 * PI * i / m - PI / 2.0;
        base[v] = {R * cos(a), R * sin(a)};
        fixed[v] = true;
        poly.push_back(base[v]);
    }

    double bestScore = -1.0;
    bool found = false;
    unsigned state = 0xC0FFEEu + 977u * (unsigned)G.N + 131u * (unsigned)outer.size();
    for (int trialNo = 0; trialNo < 7000; trialNo++) {
        vector<Point2D> trial = base;
        for (VID v : verts) {
            if (fixed[v]) continue;
            bool placed = false;
            for (int attempt = 0; attempt < 200 && !placed; attempt++) {
                double x = -R + 2.0 * R * ((double)(layoutRand(state) & 0xFFFFFFu) / (double)0xFFFFFFu);
                double y = -R + 2.0 * R * ((double)(layoutRand(state) & 0xFFFFFFu) / (double)0xFFFFFFu);
                Point2D p{x, y};
                if (pointInPolygon(p, poly)) {
                    trial[v] = p;
                    placed = true;
                }
            }
            if (!placed) {
                double a = 2.0 * PI * ((double)(layoutRand(state) & 0xFFFFFFu) / (double)0xFFFFFFu);
                double r = 0.35 * R * ((double)(layoutRand(state) & 0xFFFFFFu) / (double)0xFFFFFFu);
                trial[v] = {r * cos(a), r * sin(a)};
            }
        }
        if (!drawingIsVerified(G, trial, extraEdges)) continue;
        trial = improveInteriorLayout(G, trial, outer, extraEdges);
        trial = balanceFaceDistances(G, trial, outer, extraEdges);
        trial = improveEdgeClearance(G, trial, outer, extraEdges);
        if (!drawingIsVerified(G, trial, extraEdges)) continue;
        double score = layoutQuality(G, trial, extraEdges, &outer);
        if (!found || score > bestScore) {
            found = true;
            bestScore = score;
            out = trial;
        }
    }
    return found;
}

static bool computeVerifiedStraightLineLayout(const Graph& G, vector<Point2D>& out,
                                              const set<pair<VID,VID>>& extraEdges = {},
                                              const vector<VID>* preferredOuter = nullptr,
                                              vector<VID>* chosenOuter = nullptr) {
    // Try several outer faces and weight choices, retain the clearest verified
    // drawing, and use completion/random placement only as fallbacks.
    bool found = false;
    double bestScore = -1.0;
    vector<VID> bestFace;
    auto consider = [&](const vector<Point2D>& pos, const vector<VID>& face) {
        if (!drawingIsVerified(G, pos, extraEdges)) return;
        double score = layoutQuality(G, pos, extraEdges, face.empty() ? nullptr : &face);
        if (!found || score > bestScore) {
            found = true;
            bestScore = score;
            out = pos;
            bestFace = face;
        }
    };

    vector<vector<VID>> candidateFaces;
    vector<VID> matchedPreferred;
    bool forced = false;
    if (forced) {
        candidateFaces.push_back(matchedPreferred);
    } else if (preferredOuter && validDrawableBoundary(G, *preferredOuter, extraEdges)) {
        matchedPreferred = *preferredOuter;
        forced = true;
        candidateFaces.push_back(matchedPreferred);
    } else {
        candidateFaces = G.faces();
    }

    for (const auto& face : candidateFaces) {
        if (face.size() < 3) continue;
        if (forced && face.size() == 3 && extraEdges.empty() && isPlane3Tree(G)) {
            vector<Point2D> pos;
            if (constructAreaPlane3TreeLayout(G, face, pos, 0)) consider(pos, face);
        }
        vector<VID> reversedFace(face.rbegin(), face.rend());
        for (int mode = 0; mode <= 160; mode++) {
            vector<Point2D> pos = solveTutteLayoutForOuterFace(G, face, mode);
            consider(pos, face);
            if (forced) continue;
            pos = solveTutteLayoutForOuterFace(G, reversedFace, mode);
            consider(pos, face);
        }
    }

    if (!forced) {
        vector<Point2D> fallback = computeCircularLayout(G);
        vector<VID> emptyFace;
        consider(fallback, emptyFace);
    }
    if (!found && forced) {
        PlaneCompletionResult completion = completeToPlane3TreeByFaceInsertions(G);
        if (completion.ok) {
            for (int mode = 0; mode <= 160; mode++) {
                vector<Point2D> pos = solveTutteLayoutForOuterFace(completion.graph, matchedPreferred, mode);
                consider(pos, matchedPreferred);
            }
        }
    }
    if (!found && forced) {
        vector<Point2D> randomPos;
        if (randomInteriorLayout(G, matchedPreferred, randomPos, extraEdges)) {
            found = true;
            out = randomPos;
            bestFace = matchedPreferred;
        }
    }
    if (found && !bestFace.empty()) {
        double oldQuality = layoutQuality(G, out, extraEdges, &bestFace);
        double oldImbalance = faceDistanceImbalance(G, out);
        double oldEdgeClearance = minNonincidentEdgeDistance(G, out, extraEdges);
        vector<Point2D> improved = improveInteriorLayout(G, out, bestFace, extraEdges);
        improved = balanceFaceDistances(G, improved, bestFace, extraEdges);
        improved = improveEdgeClearance(G, improved, bestFace, extraEdges);
        double newQuality = layoutQuality(G, improved, extraEdges, &bestFace);
        double newImbalance = faceDistanceImbalance(G, improved);
        double newEdgeClearance = minNonincidentEdgeDistance(G, improved, extraEdges);
        if (drawingIsVerified(G, improved, extraEdges) &&
            (newQuality >= oldQuality ||
             (newImbalance < oldImbalance - 1e-8 && newEdgeClearance + 1e-9 >= oldEdgeClearance))) {
            out = improved;
        }
    }
    if (found && chosenOuter) *chosenOuter = bestFace;
    return found;
}

static bool writeGraphSVG(const Graph& G, const string& filename, const string& title,
                          const set<pair<VID,VID>>& extraEdges = {},
                          const set<pair<VID,VID>>& highlightEdges = {},
                          const string& highlightColor = "#005cff",
                          const string& highlightLegend = "blue = contracted edges",
                          const vector<VID>* preferredOuter = nullptr,
                          vector<VID>* chosenOuter = nullptr) {
    // Find verified coordinates, scale them to the page, and write vertices,
    // edges, labels, and optional highlighted edges as an SVG image.
    makeDir(filename.substr(0, filename.find_last_of('/')));

    vector<Point2D> pos;
    if (!computeVerifiedStraightLineLayout(G, pos, extraEdges, preferredOuter, chosenOuter)) {
        return false;
    }
    vector<VID> verts = G.aliveVertices();

    const double W = 2200.0;
    const double H = 2200.0;
    const double margin = 180.0;
    const double nodeRadius = 25.0;
    double minx = 1e100, maxx = -1e100, miny = 1e100, maxy = -1e100;
    for (VID v : verts) {
        minx = min(minx, pos[v].x); maxx = max(maxx, pos[v].x);
        miny = min(miny, pos[v].y); maxy = max(maxy, pos[v].y);
    }
    if (maxx - minx < 1e-9) { minx -= 1; maxx += 1; }
    if (maxy - miny < 1e-9) { miny -= 1; maxy += 1; }
    double scale = min((W - 2*margin) / (maxx - minx), (H - 2*margin) / (maxy - miny));
    auto sx = [&](double x) { return margin + (x - minx) * scale; };
    auto sy = [&](double y) { return H - (margin + (y - miny) * scale); };

    double minPixelVertexDist = 1e100;
    for (int i = 0; i < (int)verts.size(); i++) {
        for (int j = i + 1; j < (int)verts.size(); j++) {
            Point2D a{sx(pos[verts[i]].x), sy(pos[verts[i]].y)};
            Point2D b{sx(pos[verts[j]].x), sy(pos[verts[j]].y)};
            minPixelVertexDist = min(minPixelVertexDist, sqrt(dist2(a, b)));
        }
    }
    auto edgesForDiagnostics = drawingEdges(G, extraEdges);
    double minPixelEdgeDist = 1e100;
    for (int i = 0; i < (int)edgesForDiagnostics.size(); i++) {
        auto [a, b] = edgesForDiagnostics[i];
        Point2D pa{sx(pos[a].x), sy(pos[a].y)};
        Point2D pb{sx(pos[b].x), sy(pos[b].y)};
        for (int j = i + 1; j < (int)edgesForDiagnostics.size(); j++) {
            auto [c, d] = edgesForDiagnostics[j];
            if (a == c || a == d || b == c || b == d) continue;
            Point2D pc{sx(pos[c].x), sy(pos[c].y)};
            Point2D pd{sx(pos[d].x), sy(pos[d].y)};
            minPixelEdgeDist = min(minPixelEdgeDist, distanceSegmentSegment(pa, pb, pc, pd));
        }
    }
    ofstream out(filename);
    out << fixed << setprecision(3);
    out << "<svg xmlns='http://www.w3.org/2000/svg' width='" << W << "' height='" << H
        << "' viewBox='0 0 " << W << " " << H << "'>\n";
    out << "<rect width='100%' height='100%' fill='white'/>\n";
    out << "<!-- min vertex center distance px: " << minPixelVertexDist << " -->\n";
    out << "<!-- min nonincident edge distance px: " << minPixelEdgeDist << " -->\n";
    out << "<text x='20' y='38' font-family='Arial' font-size='28' fill='black'>"
        << title << "</text>\n";

    set<pair<VID,VID>> drawn;
    for (VID u : verts) {
        for (VID v : G.adj[u]) {
            if (v < 0 || v >= G.N || !G.alive[v]) continue;
            auto k = edgeKey(u, v);
            if (!drawn.insert(k).second) continue;
            out << "<line x1='" << sx(pos[u].x) << "' y1='" << sy(pos[u].y)
                << "' x2='" << sx(pos[v].x) << "' y2='" << sy(pos[v].y)
                << "' stroke='#333' stroke-width='1.8'/>\n";
        }
    }

    for (auto [u, v] : highlightEdges) {
        if (u < 0 || u >= G.N || v < 0 || v >= G.N || !G.alive[u] || !G.alive[v]) continue;
        if (!G.hasEdge(u, v)) continue;
        out << "<line x1='" << sx(pos[u].x) << "' y1='" << sy(pos[u].y)
            << "' x2='" << sx(pos[v].x) << "' y2='" << sy(pos[v].y)
            << "' stroke='" << highlightColor << "' stroke-width='1.8' stroke-linecap='round'/>\n";
    }

    for (auto [u, v] : extraEdges) {
        if (u < 0 || u >= G.N || v < 0 || v >= G.N || !G.alive[u] || !G.alive[v]) continue;
        if (G.hasEdge(u, v)) continue;
        out << "<line x1='" << sx(pos[u].x) << "' y1='" << sy(pos[u].y)
            << "' x2='" << sx(pos[v].x) << "' y2='" << sy(pos[v].y)
            << "' stroke='#d55e00' stroke-width='1.8' stroke-linecap='round'/>\n";
    }

    for (VID v : verts) {
        double X = sx(pos[v].x), Y = sy(pos[v].y);
        out << "<circle cx='" << X << "' cy='" << Y
            << "' r='" << nodeRadius << "' fill='white' stroke='black' stroke-width='3'/>\n";
    }
    for (VID v : verts) {
        double X = sx(pos[v].x), Y = sy(pos[v].y);
        out << "<text x='" << X << "' y='" << Y + 10
            << "' text-anchor='middle' font-family='Arial' font-size='24' font-weight='bold'"
            << " stroke='white' stroke-width='6' paint-order='stroke' fill='black'>"
            << G.name[v] << "</text>\n";
    }
    if (!extraEdges.empty()) {
        out << "<text x='20' y='" << H - 28
            << "' font-family='Arial' font-size='22' fill='#d55e00'>"
            << "orange = added edges</text>\n";
    }
    if (!highlightEdges.empty()) {
        out << "<text x='20' y='" << H - 60
            << "' font-family='Arial' font-size='22' fill='" << highlightColor << "'>"
            << highlightLegend << "</text>\n";
    }
    out << "</svg>\n";
    return true;
}

static void writeMessageSVG(const string& filename, const string& message) {
    // Write a simple placeholder SVG when a graph drawing could not be produced.
    makeDir(filename.substr(0, filename.find_last_of('/')));
    ofstream out(filename);
    out << fixed << setprecision(3);
    out << "<svg xmlns='http://www.w3.org/2000/svg' width='1200' height='260' viewBox='0 0 1200 260'>\n";
    out << "<rect width='100%' height='100%' fill='white'/>\n";
    out << "<text x='40' y='95' font-family='Arial' font-size='34' fill='black'>"
        << message << "</text>\n";
    out << "</svg>\n";
}

int main(int argc, char** argv) {
    // Command-line options control diagnostics and drawing; they do not change
    // the mathematical definition being tested.
    bool draw = false;
    bool testContractions = false;
    bool useOgdfVerify = false;
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--no-draw") {
            draw = false;
        } else if (arg == "--draw") {
            draw = true;
        } else if (arg == "--test-contractions") {
            testContractions = true;
        } else if (arg == "--ogdf-verify") {
            useOgdfVerify = true;
        } else if (arg == "--no-ogdf-verify") {
            useOgdfVerify = false;
        } else if (arg == "--help" || arg == "-h") {
            cout << "Usage: " << argv[0] << " [--draw|--no-draw] [--ogdf-verify|--no-ogdf-verify] [--test-contractions] < input.txt\n";
            cout << "  --draw     write SVG drawings\n";
            cout << "  --no-draw  skip all SVG/layout/completion drawing work (default)\n";
            cout << "  --ogdf-verify independently replay found contractions with OGDF (requires -DUSE_OGDF build)\n";
            cout << "  --no-ogdf-verify disable OGDF replay verification (default)\n";
            cout << "  --test-contractions  compare both directions of every one-edge contraction\n";
            return 0;
        } else {
            cerr << "Unknown option: " << arg << "\n";
            cerr << "Usage: " << argv[0] << " [--draw|--no-draw] [--ogdf-verify|--no-ogdf-verify] [--test-contractions] < input.txt\n";
            return 2;
        }
    }

#ifndef USE_OGDF
    if (useOgdfVerify) {
        cerr << "ERROR: --ogdf-verify was requested, but this binary was not compiled with -DUSE_OGDF.\n";
        cerr << "Recompile with OGDF include/library paths, or run without --ogdf-verify.\n";
        return 2;
    }
#endif

    vector<string> inputs;
    string line;
    while (getline(cin, line)) {
        if (!isBlankLine(line)) inputs.push_back(line);
    }

    if (inputs.empty()) {
        cout << "No graph input provided.\n";
        return 0;
    }

    if (draw) {
        clearDrawingDirectory();
    }

    bool allTrue = true;
    for (int idx = 0; idx < (int)inputs.size(); idx++) {
        cout << "\n=== Graph " << (idx + 1) << " ===\n";
        cout << inputs[idx] << "\n";

        try {
            Graph G = parseASCII(inputs[idx]);
            string validationMessage;
            if (!validateInputGraph(G, validationMessage)) {
                cout << "ERROR: invalid input embedding: " << validationMessage << "\n";
                allTrue = false;
                continue;
            }
            if (testContractions) {
                cout << "contraction direction diagnostic:\n";
                if (!testContractionDirectionConsistency(G, (int)G.faces().size() / 2, cout)) allTrue = false;
            }
            vector<VID> initialOuterFace;
            string dir;
            string svgFile;
            if (draw) {
                dir = graphDirName(idx + 1);
                makeDir(dir);
                svgFile = dir + "/initial.svg";
                if (writeGraphSVG(G, svgFile, string("Initial graph ") + to_string(idx + 1),
                                  {}, {}, "#005cff", "blue = contracted edges",
                                  nullptr, &initialOuterFace)) {
                    cout << "initial drawing: " << svgFile << "\n";
                    if (!initialOuterFace.empty()) {
                        cout << "drawing outer face: " << faceNames(G, initialOuterFace) << "\n";
                    }
                } else {
                    cout << "initial drawing: FAILED to find verified crossing-free straight-line layout\n";
                }
            }

            int faceCount = (int)G.faces().size();
            cout << "vertices: " << G.aliveVertices().size()
                 << ", faces: " << faceCount << "\n";

            if (!allFacesQuadrangles(G)) {
                cout << "FALSE (not every face in the embedding is a quadrangle)\n";
                allTrue = false;
                continue;
            }

            // Integer division is floor(|F|/2).
            int target = faceCount / 2;
            cout << "max contractions: " << target << "\n";

            // Search every branch to its limit or first contraction-free leaf;
            // only those leaf graphs are tested as partial 3-trees.
            SearchResult r = searchContractions(G, target);
            if (r.found) {
#ifdef USE_OGDF
                if (useOgdfVerify) {
                    string ogdfVerifierMessage;
                    bool ogdfVerified = verifyContractionCertificateOgdf(G, r, ogdfVerifierMessage);
                    if (!ogdfVerified) {
                        cout << "OGDF VERIFICATION FAILED for graph " << (idx + 1)
                             << ": " << ogdfVerifierMessage << "\n";
                        allTrue = false;
                    }
                }
#endif
                cout << "TRUE\n";
                cout << "contractions:";
                for (const string& e : r.contractions) cout << " " << e;
                cout << "\n";
                cout << "contracted graph: " << toCompactASCII(r.finalGraph) << "\n";
                cout << "contracted graph with original labels: " << toOriginalLabelASCII(r.finalGraph) << "\n";

                if (draw) {
                    vector<VID> contractedOuterFace = transformedFaceAfterContractions(
                        G, initialOuterFace, r.directedContractions);
                    if (!contractedOuterFace.empty()) {
                        cout << "transformed initial outer face: " << faceNames(r.finalGraph, contractedOuterFace) << "\n";
                    }
                    set<pair<VID,VID>> contractionHighlightEdges;
                    for (auto e : r.contractionEdges) {
                        if (G.hasEdge(e.first, e.second)) contractionHighlightEdges.insert(e);
                    }
                    if (!contractionHighlightEdges.empty()) {
                        if (writeGraphSVG(G, svgFile,
                                          string("Initial graph ") + to_string(idx + 1) + " with contracted edges",
                                          {}, contractionHighlightEdges,
                                          "#005cff", "blue = contracted edges",
                                          initialOuterFace.empty() ? nullptr : &initialOuterFace)) {
                            cout << "initial drawing updated with contracted-edge highlights: " << svgFile << "\n";
                        }
                    }
                    string contractedSvg = dir + "/contracted.svg";
                    vector<VID> contractedChosenOuter;
                    if (writeGraphSVG(r.finalGraph, contractedSvg,
                                      string("Contracted graph ") + to_string(idx + 1),
                                      {}, {}, "#005cff", "blue = contracted edges",
                                      contractedOuterFace.empty() ? nullptr : &contractedOuterFace,
                                      &contractedChosenOuter)) {
                        cout << "contracted drawing: " << contractedSvg << "\n";
                        if (!contractedChosenOuter.empty()) {
                            cout << "contracted drawing outer face: "
                                 << faceNames(r.finalGraph, contractedChosenOuter) << "\n";
                        }
                    } else {
                        cout << "contracted drawing: FAILED to find verified crossing-free straight-line layout\n";
                    }

                    string completionSvg = dir + "/completion.svg";
                    PlaneCompletionResult planeCompletion = completeToPlane3TreeByFaceInsertions(
                        r.finalGraph,
                        contractedOuterFace.empty() ? nullptr : &contractedOuterFace,
                        0);
                    vector<VID> completionChosenOuter;
                    bool completionDrawn = false;
                    if (planeCompletion.ok) {
                        vector<VID> completionOuterFace = completionOuterBoundary(
                            planeCompletion.graph, contractedOuterFace, planeCompletion.addedEdges);
                        completionDrawn = writeGraphSVG(planeCompletion.graph, completionSvg,
                                                        string("Embedding-preserving plane 3-tree completion for graph ") + to_string(idx + 1),
                                                        {}, planeCompletion.addedEdges,
                                                        "#d55e00", "orange = inserted completion edges",
                                                        completionOuterFace.empty() ? nullptr : &completionOuterFace,
                                                        &completionChosenOuter);
                    }
                    if (completionDrawn) {
                        cout << "completion drawing: " << completionSvg << "\n";
                        if (!completionChosenOuter.empty()) {
                            cout << "completion drawing outer face: "
                                 << faceNames(planeCompletion.graph, completionChosenOuter) << "\n";
                        }
                    } else if (planeCompletion.ok) {
                        cout << "completion drawing: FAILED to draw verified straight-line completion\n";
                        writeMessageSVG(completionSvg, "Failed to draw completion without edge overlap");
                    } else {
                        cout << "completion drawing: FAILED to construct embedding-preserving plane 3-tree completion\n";
                        writeMessageSVG(completionSvg, "Failed to construct embedding-preserving plane 3-tree completion");
                    }
                    cout << "added completion edges:";
                    for (auto [u, v] : planeCompletion.addedEdges) {
                        cout << " " << r.finalGraph.name[u] << r.finalGraph.name[v];
                    }
                    cout << "\n";
                } else {
                    cout << "drawings skipped (--no-draw)\n";
                }
            } else {
                cout << "FALSE\n";
                allTrue = false;
            }
        } catch (const exception& e) {
            cout << "ERROR: " << e.what() << "\n";
            allTrue = false;
        }
    }

    cout << "\nOverall result: " << (allTrue ? "TRUE" : "FALSE") << "\n";
    return allTrue ? 0 : 1;
}
