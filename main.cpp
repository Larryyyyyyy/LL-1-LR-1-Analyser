#include <cstdio>
#include <cstring>
#include <string>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <algorithm>
#include <vector>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <unordered_set>
#include <unordered_map>
#define Production std::vector<std::string>
#define Action std::pair<SLRAction, int>
#define FollowSymbols std::unordered_set<std::string>

const std::string START = "START";
std::string s;
std::string start_symbol;
int production_index = 0;
bool enable_solve_left_recursion;
bool is_left_recursion;
enum class State: int { TerminalSymbol, Non_TerminalSymbol, StartSymbol, Productions, EnableSolveLeftRecursion, LL1Sentence, LR1Sentence, End };
enum class Symbol: int { TerminalSymbol, Non_TerminalSymbol };
enum class Epsilon: int {Yes, No, Uncertained};
enum class SLRAction: int {S, R, Accept};
enum class Recursion: int {True, False, Replace};
std::unordered_map<std::string, Symbol> symbols;
std::unordered_map<std::string, Epsilon> can_be_epsilon;
std::vector<std::string> terminal_symbols;
std::vector<std::string> non_terminal_symbols;
std::unordered_map<std::string, std::vector<std::pair<int, Production>>> productions;
std::unordered_map<std::string, std::set<std::string>> first;
std::unordered_map<std::string, std::set<std::string>> follow;
std::map<std::pair<std::string, std::string>, Production> predict_table;
std::vector<std::vector<std::string>> ll1sentence;
std::vector<std::vector<std::string>> lr1sentence;
std::vector<std::pair<std::vector<Production>, std::vector<Production>>> closure_slr1;
std::map<std::pair<int, std::string>, int> goto_slr1;
std::map<std::pair<int, std::string>, Action> analysis_table_slr1;
std::vector<std::pair<std::vector<std::pair<Production, FollowSymbols>>, std::vector<std::pair<Production, FollowSymbols>>>> closure_lr1;
std::map<std::pair<int, std::string>, int> goto_lr1;
std::map<std::pair<int, std::string>, Action> analysis_table_lr1;
std::vector<std::pair<std::vector<std::pair<Production, FollowSymbols>>, std::vector<std::pair<Production, FollowSymbols>>>> closure_lalr1;
std::map<std::pair<int, std::string>, int> goto_lalr1;
std::map<std::pair<int, std::string>, Action> analysis_table_lalr1;

bool isblank(const std::string &s) {
    for(int i = 0; i < s.size(); ++i) {
        if (s[i] != ' ' && s[i] != '\t' && s[i] != '\n') {
            return false;
        }
    }
    return true;
}
bool is_terminal_symbols(const std::string &s) {
    return symbols[s] == Symbol::TerminalSymbol;
}
bool is_non_terminal_symbols(const std::string &s) {
    return symbols[s] == Symbol::Non_TerminalSymbol;
}
bool parse_terminalsymbol(const std::string &s) {
    const std::string model = "Terminal Symbol";
    if (s != model) return false;
    std::string line, temp;
    std::getline(std::cin, line);
    for (int i = 0; i < line.size(); ++i) {
        if (line[i] == ' ') {
            if (temp == "") return false;
            symbols[temp] = Symbol::TerminalSymbol;
            terminal_symbols.push_back(temp);
            temp = "";
        } else {
            temp += line[i];
        }
    }
    symbols[temp] = Symbol::TerminalSymbol;
    terminal_symbols.push_back(temp);
    return true;
}
bool parse_non_terminalsymbol(const std::string &s) {
    const std::string model = "Non-Terminal Symbol";
    if (s != model) return false;
    std::string line, temp;
    std::getline(std::cin, line);
    for (int i = 0; i < line.size(); ++i) {
        if (line[i] == ' ') {
            if (temp == "") return false;
            symbols[temp] = Symbol::Non_TerminalSymbol;
            non_terminal_symbols.push_back(temp);
            can_be_epsilon[temp] = Epsilon::Uncertained;
            temp = "";
        } else {
            temp += line[i];
        }
    }
    symbols[temp] = Symbol::Non_TerminalSymbol;
    non_terminal_symbols.push_back(temp);
    can_be_epsilon[temp] = Epsilon::Uncertained;
    return true;
}
bool parse_startsymbol(const std::string &s) {
    const std::string model = "Start Symbol";
    if (s != model) return false;
    std::string line;
    std::getline(std::cin, line);
    if (is_terminal_symbols(line)) {
        puts("Start symbol is not non-terminalsymbol.");
        return false;
    }
    start_symbol = line;
    return true;
}
bool parse_productions(const std::string &s) {
    enum class production: int { Left, Arrow, Right };
    const std::string model = "Productions";
    if (s != model) return false;
    production state = production::Left;
    std::string line, temp, now;
    while(std::getline(std::cin, line)) {
        if (isblank(line)) return true;
        std::vector<std::string> production;
        for (int i = 0; i < line.size(); ++i) {
            if (line[i] == ' ') {
                if (state == production::Left) {
                    if (symbols[temp] != Symbol::Non_TerminalSymbol) {
                        return false;
                    }
                    state = production::Arrow;
                    now = temp;
                } else {
                    if (state == production::Arrow) {
                        if (temp != "\\to") {
                            return false;
                        }
                        state = production::Right;
                    } else {
                        if (symbols.find(temp) == symbols.end()) {
                            return false;
                        }
                        if (temp == "\\epsilon") {
                            can_be_epsilon[now] = Epsilon::Yes;
                        }
                        production.push_back(temp);
                    }
                }
                temp = "";
            } else {
                temp += line[i];
            }
        }
        production.push_back(temp);
        productions[now].push_back({++production_index, production});
        state = production::Left;
        temp = "";
    }
    return true;
}
bool parse_enablesolveleftrecursion(const std::string &s) {
    const std::string model = "Enable Solve Left Recursion";
    if (s != model) return false;
    std::string line;
    std::getline(std::cin, line);
    if (line == "true") {
        enable_solve_left_recursion = true;
    }
    return true;
}
bool parse_ll1sentence(const std::string &s) {
    const std::string model = "LL(1) Sentence";
    if (s != model) return false;
    std::string line, temp;
    std::vector<std::string> sentence;
    while(std::getline(std::cin, line)) {
        if (isblank(line)) return true;
        for (int i = 0; i < line.size(); ++i) {
            if (line[i] == ' ') {
                sentence.push_back(temp);
                temp = "";
            } else {
                temp += line[i];
            }
        }
        sentence.push_back(temp);
        ll1sentence.push_back(sentence);
        sentence.clear();
        temp = "";
    }
    return true;
}
bool parse_slr1sentence(const std::string &s) {
    const std::string model = "SLR(1) Sentence";
    if (s != model) return false;
    std::string line, temp;
    std::vector<std::string> sentence;
    while(std::getline(std::cin, line)) {
        if (isblank(line)) return true;
        for (int i = 0; i < line.size(); ++i) {
            if (line[i] == ' ') {
                sentence.push_back(temp);
                temp = "";
            } else {
                temp += line[i];
            }
        }
        sentence.push_back(temp);
        lr1sentence.push_back(sentence);
        sentence.clear();
        temp = "";
    }
    return true;
}
int getindex(Production production) {
    auto equal_ignoring_dot = [](const Production& left, const Production& right) {
        auto i = left.begin();
        auto j = right.begin();
        while (true) {
            while (i != left.end() && *i == "\\cdot") ++i;
            while (j != right.end() && *j == "\\cdot") ++j;
            if (i == left.end() || j == right.end()) {
                return i == left.end() && j == right.end();
            }
            if (*i != *j) return false;
            ++i;
            ++j;
        }
    };
    for (auto p:productions) {
        if (p.first != production[0]) continue;
        for (auto production_:p.second) {
            if (equal_ignoring_dot(production_.second, Production(production.begin() + std::min<std::size_t>(2, production.size()), production.end()))) {
                return production_.first;
            }
        }
    }
    puts("Get index error!");
    return -1;
}
std::pair<std::string, Production> getproduction(int index) {
    for (const auto &non_terminal_symbol:non_terminal_symbols) {
        for (const auto &production:productions[non_terminal_symbol]) {
            if (production.first == index) {
                return {non_terminal_symbol, production.second};
            }
        }
    }
    puts("Get production error!");
    return {};
}
bool initial() {
    State state = State::TerminalSymbol;
    while(std::getline(std::cin, s)) {
        if (isblank(s)) continue;
        if (s.substr(0, 2) == "//") continue;
        switch (state) {
            case State::TerminalSymbol:
                if (!parse_terminalsymbol(s)) {
                    puts("Parse terminal symbol error!");
                    return false;
                }
                state = State::Non_TerminalSymbol;
                break;
            case State::Non_TerminalSymbol:
                if (!parse_non_terminalsymbol(s)) {
                    puts("Parse non-terminal symbol error!");
                    return false;
                }
                state = State::StartSymbol;
                break;
            case State::StartSymbol:
                if (!parse_startsymbol(s)) {
                    puts("Parse start symbol error!");
                    return false;
                }
                state = State::Productions;
                break;
            case State::Productions:
                if (!parse_productions(s)) {
                    puts("Parse productions error!");
                    return false;
                }
                state = State::EnableSolveLeftRecursion;
                break;
            case State::EnableSolveLeftRecursion:
                if (!parse_enablesolveleftrecursion(s)) {
                    puts("Parse enable solve left recursion error!");
                    return false;
                }
                state = State::LL1Sentence;
                break;
            case State::LL1Sentence:
                if (!parse_ll1sentence(s)) {
                    puts("Parse LL(1) Sentence error!");
                    return false;
                }
                state = State::LR1Sentence;
                break;
            case State::LR1Sentence:
                if (!parse_slr1sentence(s)) {
                    puts("Parse SLR(1) Sentence error!");
                    return false;
                }
                state = State::End;
                break;
        }
    }
    return true;
}
void confirm_epsilon() {
    for (int i = 1; i <= productions.size(); ++i) {
        bool finished = true;
        for (auto non_terminal_symbol:non_terminal_symbols) {
            if (can_be_epsilon[non_terminal_symbol] != Epsilon::Uncertained) continue;
            finished = false;
            bool is_no = true;
            for (auto production:productions[non_terminal_symbol]) {
                auto is_epsilon = Epsilon::Yes;
                for (auto symbol:production.second) {
                    if (symbols[symbol] == Symbol::TerminalSymbol) {
                        if (symbol == "\\epsilon") {
                            is_epsilon = Epsilon::Yes;
                        } else {
                            is_epsilon = Epsilon::No;
                        }
                        break;
                    }
                    if (can_be_epsilon[symbol] == Epsilon::No) {
                        is_epsilon = Epsilon::No;
                        break;
                    }
                    if (can_be_epsilon[symbol] == Epsilon::Uncertained) {
                        is_epsilon = Epsilon::Uncertained;
                    }
                }
                if (is_epsilon == Epsilon::Yes) {
                    can_be_epsilon[non_terminal_symbol] = Epsilon::Yes;
                    is_no = false;
                    break;
                }
                if (is_epsilon == Epsilon::Uncertained) {
                    is_no = false;
                }
            }
            if (is_no) {
                can_be_epsilon[non_terminal_symbol] = Epsilon::No;
            }
        }
        if (finished) break;
    }
    for (auto &p:can_be_epsilon) {
        if (p.second == Epsilon::Uncertained) {
            p.second = Epsilon::No;
        }
    }
}
bool getfirst() {
    std::unordered_map<std::string, FollowSymbols> out;
    for (const auto& non_terminal_symbol : non_terminal_symbols) {
        for (const auto& production : productions[non_terminal_symbol]) {
            for (const auto& in_symbol : production.second) {
                if (is_terminal_symbols(in_symbol)) {
                    first[non_terminal_symbol].insert(in_symbol);
                    break;
                } else {
                    if (in_symbol != non_terminal_symbol) {
                        out[in_symbol].insert(non_terminal_symbol);
                    }
                    if (can_be_epsilon[in_symbol] == Epsilon::Yes) {
                        continue;
                    } else {
                        break;
                    }
                }
            }
        }
    }
    std::unordered_map<std::string, int> dfn, low;
    std::unordered_map<std::string, bool> in_stack;
    std::vector<std::string> stk;
    int dfn_cnt = 0;
    int scc_cnt = 0;
    std::unordered_map<std::string, int> scc_id;
    std::vector<std::vector<std::string>> scc_nodes;
    auto tarjan = [&](auto& self, const std::string& u) -> void {
        dfn[u] = low[u] = ++dfn_cnt;
        stk.push_back(u);
        in_stack[u] = true;
        if (out.count(u)) {
            for (const auto& v : out[u]) {
                if (!dfn.count(v)) {
                    self(self, v);
                    low[u] = std::min(low[u], low[v]);
                } else if (in_stack[v]) {
                    low[u] = std::min(low[u], dfn[v]);
                }
            }
        }
        if (dfn[u] == low[u]) {
            scc_nodes.emplace_back();
            while (true) {
                std::string v = stk.back();
                stk.pop_back();
                in_stack[v] = false;
                scc_id[v] = scc_cnt;
                scc_nodes[scc_cnt].push_back(v);
                if (u == v) break;
            }
            if (scc_nodes[scc_cnt].size() > 1) {
                is_left_recursion = true;
            }
            scc_cnt++;
        }
    };
    for (const auto& nt : non_terminal_symbols) {
        if (!dfn.count(nt)) {
            tarjan(tarjan, nt);
        }
    }
    std::vector<std::set<std::string>> scc_first(scc_cnt);
    for (int i = 0; i < scc_cnt; ++i) {
        for (const auto& nt : scc_nodes[i]) {
            scc_first[i].insert(first[nt].begin(), first[nt].end());
        }
    }
    std::vector<std::unordered_set<int>> dag_out(scc_cnt);
    std::vector<int> dag_in(scc_cnt, 0);
    for (const auto& item:out) {
        int u_id = scc_id[item.first];
        for (const auto& v:item.second) {
            int v_id = scc_id[v];
            if (u_id != v_id) {
                if (dag_out[u_id].insert(v_id).second) {
                    dag_in[v_id]++;
                }
            }
        }
    }
    std::queue<int> q;
    for (int i = 0; i < scc_cnt; ++i) {
        if (dag_in[i] == 0) {
            q.push(i);
        }
    }
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        for (int v : dag_out[u]) {
            scc_first[v].insert(scc_first[u].begin(), scc_first[u].end());
            dag_in[v]--;
            if (dag_in[v] == 0) {
                q.push(v);
            }
        }
    }
    for (const auto& nt:non_terminal_symbols) {
        int id = scc_id[nt];
        first[nt] = scc_first[id];
    }
    puts("FIRST");
    for (auto non_terminal_symbol:non_terminal_symbols) {
        std::cout << non_terminal_symbol << ": ";
        for (auto f:first[non_terminal_symbol]) {
            if (f == "\\epsilon") f = "ε";
            std::cout << f << " ";
        }
        puts("");
    }
    puts("");
    return is_left_recursion;
}
void getfollow() {
    std::unordered_map<std::string, std::set<std::string>> out;
    follow[start_symbol].insert("$");
    for (const auto& non_terminal_symbol : non_terminal_symbols) {
        for (const auto& production : productions[non_terminal_symbol]) {
            for (size_t i = 0; i < production.second.size(); ++i) {
                auto now = production.second[i];
                if (is_terminal_symbols(now)) {
                    continue;
                }
                bool keep_epsilon = true;
                for (size_t j = i + 1; j < production.second.size(); ++j) {
                    auto symbol = production.second[j];
                    if (is_terminal_symbols(symbol)) {
                        follow[now].insert(symbol);
                        keep_epsilon = false;
                        break;
                    } else {
                        follow[now].insert(first[symbol].begin(), first[symbol].end());
                        follow[now].erase("\\epsilon");
                        if (can_be_epsilon[symbol] == Epsilon::No) {
                            keep_epsilon = false;
                            break;
                        }
                    }
                }
                if (keep_epsilon && non_terminal_symbol != now) {
                    out[non_terminal_symbol].insert(now);
                }
            }
        }
    }
    std::unordered_map<std::string, int> dfn, low;
    std::unordered_map<std::string, bool> in_stack;
    std::vector<std::string> stk;
    int dfn_cnt = 0;
    int scc_cnt = 0;
    std::unordered_map<std::string, int> scc_id;
    std::vector<std::vector<std::string>> scc_nodes;
    auto tarjan = [&](auto& self, const std::string& u) -> void {
        dfn[u] = low[u] = ++dfn_cnt;
        stk.push_back(u);
        in_stack[u] = true;
        if (out.count(u)) {
            for (const auto& v : out[u]) {
                if (!dfn.count(v)) {
                    self(self, v);
                    low[u] = std::min(low[u], low[v]);
                } else if (in_stack[v]) {
                    low[u] = std::min(low[u], dfn[v]);
                }
            }
        }
        if (dfn[u] == low[u]) {
            scc_nodes.emplace_back();
            while (true) {
                std::string v = stk.back();
                stk.pop_back();
                in_stack[v] = false;
                scc_id[v] = scc_cnt;
                scc_nodes[scc_cnt].push_back(v);
                if (u == v) break;
            }
            scc_cnt++;
        }
    };
    for (const auto& nt : non_terminal_symbols) {
        if (!dfn.count(nt)) {
            tarjan(tarjan, nt);
        }
    }
    std::vector<std::set<std::string>> scc_follow(scc_cnt);
    for (int i = 0; i < scc_cnt; ++i) {
        for (const auto& nt : scc_nodes[i]) {
            scc_follow[i].insert(follow[nt].begin(), follow[nt].end());
        }
    }
    std::vector<std::set<int>> dag_out(scc_cnt);
    std::vector<int> dag_in(scc_cnt, 0);
    for (const auto& item:out) {
        int u_id = scc_id[item.first];
        for (const auto& v : item.second) {
            int v_id = scc_id[v];
            if (u_id != v_id) {
                if (dag_out[u_id].insert(v_id).second) {
                    dag_in[v_id]++;
                }
            }
        }
    }
    std::queue<int> q;
    for (int i = 0; i < scc_cnt; ++i) {
        if (dag_in[i] == 0) {
            q.push(i);
        }
    }
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        for (int v : dag_out[u]) {
            scc_follow[v].insert(scc_follow[u].begin(), scc_follow[u].end());
            dag_in[v]--;
            if (dag_in[v] == 0) {
                q.push(v);
            }
        }
    }
    for (const auto& nt:non_terminal_symbols) {
        int id = scc_id[nt];
        follow[nt] = scc_follow[id];
    }
    puts("FOLLOW");
    for (const auto &non_terminal_symbol:non_terminal_symbols) {
        std::cout << non_terminal_symbol << ": ";
        for (auto f:follow[non_terminal_symbol]) {
            std::cout << f << " ";
        }
        puts("");
    }
    puts("");
}
bool checkLL1() {
    for (const auto &non_terminal_symbol:non_terminal_symbols) {
        auto len = productions[non_terminal_symbol].size();
        if (len <= 1) continue;
        std::vector<std::set<std::string>> s;
        bool check_epsilon = false;
        for (int i = 0; i < len; ++i) {
            std::set<std::string> sfirst;
            bool all_epsilon = true;
            for (const auto &symbol:productions[non_terminal_symbol][i].second) {
                if (is_terminal_symbols(symbol)) {
                    sfirst.insert(symbol);
                    all_epsilon = false;
                    break;
                } else {
                    sfirst.insert(first[symbol].begin(), first[symbol].end());
                    sfirst.erase("\\epsilon");
                    if (can_be_epsilon[symbol] == Epsilon::No) {
                        all_epsilon = false;
                        break;
                    }
                }
            }
            if (all_epsilon) {
                check_epsilon = true;
                sfirst.insert("\\epsilon");
            }
            s.push_back(sfirst);
        }
        for (int i = 0; i < len; ++i) {
            for (int j = i + 1; j < len; ++j) {
                for (const auto& symbol:s[i]) {
                    if (s[j].count(symbol)) {
                        return false;
                    }
                }
            }
        }
        if (check_epsilon) {
            for (int i = 0; i < len; ++i) {
                if (s[i].find("\\epsilon") != s[i].end()) continue;
                for (const auto& symbol:s[i]) {
                    if (follow[non_terminal_symbol].count(symbol)) return false;
                }
            }
        }
    }
    return true;
}
void construct_predict_table() {
    for (const auto &non_terminal_symbol:non_terminal_symbols) {
        auto len = productions[non_terminal_symbol].size();
        std::vector<std::set<std::string>> s;
        for (int i = 0; i < len; ++i) {
            auto symbol = productions[non_terminal_symbol][i].second[0];
            if (symbol == "\\epsilon") {
                for (auto terminal_symbol:follow[non_terminal_symbol]) {
                    predict_table[{non_terminal_symbol, terminal_symbol}] = productions[non_terminal_symbol][i].second;
                }
                continue;
            }
            if (is_non_terminal_symbols(symbol)) {
                for (auto terminal_symbol:first[symbol]) {
                    predict_table[{non_terminal_symbol, terminal_symbol}] = productions[non_terminal_symbol][i].second;
                }
            } else {
                predict_table[{non_terminal_symbol, symbol}] = productions[non_terminal_symbol][i].second;
            }
        }
    }
    for (const auto &prediction:predict_table) {
        std::cout << "Prediction[" << prediction.first.first << ", " << prediction.first.second << "] = " << prediction.first.first << " → ";
        for (auto symbol:prediction.second) {
            if (symbol == "\\epsilon") symbol = "ε";
            std::cout << symbol << " ";
        }
        puts("");
    }
    puts("");
}
void analyse_ll1_sentence() {
    for (auto sentence:ll1sentence) {
        std::cout << "Analyse ";
        for (const auto &symbol:sentence) {
            std::cout << symbol << " ";
        }
        puts(":");
        std::stack<std::string> stack;
        stack.push(start_symbol);
        sentence.push_back("$");
        for (int i = 0; i < sentence.size(); ++i) {
            while(!stack.empty() && stack.top() != sentence[i]) {
                auto stack_copy = stack;
                std::vector<std::string> stack_items;
                while (!stack_copy.empty()) {
                    stack_items.push_back(stack_copy.top());
                    stack_copy.pop();
                }
                for (auto it = stack_items.rbegin(); it != stack_items.rend(); ++it) {
                    if (*it == "\\epsilon") std::cout << "ε" << " ";
                    else std::cout << *it << " ";
                }
                std::cout << "| " << sentence[i] << std::endl;
                auto production = predict_table[{stack.top(), sentence[i]}];
                stack.pop();
                for (int j = production.size() - 1; j >= 0; --j) {
                    if (production[j] != "\\epsilon") {
                        stack.push(production[j]);
                    }
                }
            }
            auto stack_copy = stack;
            std::vector<std::string> stack_items;
            while (!stack_copy.empty()) {
                stack_items.push_back(stack_copy.top());
                stack_copy.pop();
            }
            for (auto it = stack_items.rbegin(); it != stack_items.rend(); ++it) {
                if (*it == "\\epsilon") std::cout << "ε" << " ";
                else std::cout << *it << " ";
            }
            if (!stack.empty()) {
                stack.pop();
                std::cout << "| " << sentence[i] << std::endl;
            } else {
                std::cout << "accept" << std::endl;
                puts("");
            }
        }
    }
}
void argumentation_grammar() {
    symbols[START] = Symbol::Non_TerminalSymbol;
    can_be_epsilon[START] = can_be_epsilon[start_symbol];
    non_terminal_symbols.push_back(START);
    productions[START].push_back({0, {start_symbol}});
    first[START] = first[start_symbol];
    follow[START] = follow[start_symbol];
}
void export_to_dot_slr1(const std::string& filename = "./example/slr_dfa.dot") {
    std::ofstream out(filename);
    if (!out.is_open()) {
        std::cerr << "Failed to open " << filename << " for dot export.\n";
        return;
    }
    out << "digraph LR0_DFA {\n";
    out << "    rankdir=LR;\n";
    out << "    node [shape=box, fontname=\"Courier\", style=\"rounded,filled\", fillcolor=\"#f8f9fa\"];\n";
    out << "    edge [fontname=\"Courier\", fontsize=10];\n\n";
    for (int i = 0; i < closure_slr1.size(); ++i) {
        out << "    I" << i << " [shape=none, label=<\n";
        out << "        <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\" COLOR=\"#B0BEC5\">\n";
        out << "            <TR><TD BGCOLOR=\"#37474F\" ALIGN=\"CENTER\"><FONT COLOR=\"#FFFFFF\"><B>I<SUB>" 
            << i << "</SUB></B></FONT></TD></TR>\n";
        auto format_item_text = [](const Production& prod) {
            std::string text;
            for (auto symbol : prod) {
                if (symbol == "\\to") symbol = "-&gt;";        // 转义 > 为 -&gt;
                else if (symbol == "\\cdot") symbol = "·";
                else if (symbol == "\\epsilon") symbol = "ε";
                else if (symbol == "<") symbol = "&lt;";
                else if (symbol == ">") symbol = "&gt;";
                else if (symbol == "&") symbol = "&amp;";
                text += symbol + " ";
            }
            return text;
        };
        for (const auto& prod : closure_slr1[i].first) {
            out << "            <TR><TD BGCOLOR=\"#E3F2FD\" ALIGN=\"LEFT\"><FONT COLOR=\"#0D47A1\"><B>"
                << format_item_text(prod)
                << "</B></FONT></TD></TR>\n";
        }
        if (!closure_slr1[i].first.empty() && !closure_slr1[i].second.empty()) {
            out << "            <HR/>\n";
        }
        for (const auto& prod : closure_slr1[i].second) {
            out << "            <TR><TD BGCOLOR=\"#FAFAFA\" ALIGN=\"LEFT\"><FONT COLOR=\"#616161\">"
                << format_item_text(prod)
                << "</FONT></TD></TR>\n";
        }
        out << "        </TABLE>\n";
        out << "    >];\n";
    }
    out << "\n";
    for (const auto& edge : goto_slr1) {
        int u = edge.first.first;
        std::string symbol = edge.first.second;
        int v = edge.second;
        if (symbol == "\\epsilon") symbol = "ε";
        if (symbol == "\"") symbol = "\\\"";
        out << "    I" << u << " -> I" << v << " [label=\"" << symbol << "\"];\n";
    }
    out << "}\n";
    out.close();
}
void construct_slr1_closure() {
    closure_slr1.push_back({{{START, "\\to", "\\cdot", start_symbol}}, {}});
    for (int i = 0;; ++i) {
        if (i >= closure_slr1.size()) break;
        std::unordered_map<std::string, std::vector<Production>> out_productions;
        for (auto production:closure_slr1[i].first) {
            auto cdot_position = std::find(production.begin(), production.end(), "\\cdot") - production.begin();
            if (cdot_position + 1 == production.size()) {
                continue;
            }
            auto symbol = production[cdot_position + 1];
            swap(production[cdot_position], production[cdot_position + 1]);
            if (is_non_terminal_symbols(symbol)) {
                for (auto production_right:productions[symbol]) {
                    Production s = {symbol, "\\to", "\\cdot"};
                    s.insert(s.end(), production_right.second.begin(), production_right.second.end());
                    if (std::find(closure_slr1[i].second.begin(), closure_slr1[i].second.end(), s) == closure_slr1[i].second.end()) {
                        closure_slr1[i].second.push_back(s);
                    }
                }
            }
            out_productions[production[cdot_position]].push_back(production);
        }
        for (int t = 0;; ++t) {
            if (t >= closure_slr1[i].second.size()) break;
            bool detect_cdot = false;
            auto production = closure_slr1[i].second[t];
            auto cdot_position = std::find(production.begin(), production.end(), "\\cdot") - production.begin();
            if (cdot_position + 1 == production.size()) {
                continue;
            }
            auto symbol = production[cdot_position + 1];
            swap(production[cdot_position], production[cdot_position + 1]);
            if (is_non_terminal_symbols(symbol)) {
                for (auto production_right:productions[symbol]) {
                    Production s = {symbol, "\\to", "\\cdot"};
                    s.insert(s.end(), production_right.second.begin(), production_right.second.end());
                    if (std::find(closure_slr1[i].second.begin(), closure_slr1[i].second.end(), s) == closure_slr1[i].second.end()) {
                        closure_slr1[i].second.push_back(s);
                    }
                }
            }
            out_productions[production[cdot_position]].push_back(production);
        }
        for (const auto &symbol:terminal_symbols) {
            if (out_productions[symbol].empty()) {
                continue;
            }
            bool prev_exist = false;
            for (int closure_index = 0; closure_index < closure_slr1.size(); ++closure_index) {
                const auto &closure = closure_slr1[closure_index];
                bool found = !out_productions[symbol].empty() && closure.first.size() == out_productions[symbol].size();
                if (found) {
                    for (const auto &production:closure.first) {
                        if (std::find(out_productions[symbol].begin(), out_productions[symbol].end(), production) == out_productions[symbol].end()) {
                            found = false;
                            break;
                        }
                    }
                }
                if (found) {
                    goto_slr1[{i, symbol}] = closure_index;
                    prev_exist = true;
                    break;
                }
            }
            if (!prev_exist) {
                goto_slr1[{i, symbol}] = closure_slr1.size();
                closure_slr1.push_back({out_productions[symbol], {}});
            }
        }
        for (const auto symbol:non_terminal_symbols) {
            if (out_productions[symbol].empty()) {
                continue;
            }
            bool prev_exist = false;
            for (int closure_index = 0; closure_index < closure_slr1.size(); ++closure_index) {
                const auto &closure = closure_slr1[closure_index];
                bool found = !out_productions[symbol].empty() && closure.first.size() == out_productions[symbol].size();
                if (found) {
                    for (const auto &production:closure.first) {
                        if (std::find(out_productions[symbol].begin(), out_productions[symbol].end(), production) == out_productions[symbol].end()) {
                            found = false;
                            break;
                        }
                    }
                }
                if (found) {
                    goto_slr1[{i, symbol}] = closure_index;
                    prev_exist = true;
                    break;
                }
            }
            if (!prev_exist) {
                goto_slr1[{i, symbol}] = closure_slr1.size();
                closure_slr1.push_back({out_productions[symbol],{}});
            }
        }
    }
    export_to_dot_slr1();
}
void print_slr_table() {
    std::vector<std::string> action_cols = terminal_symbols;
    if (std::find(action_cols.begin(), action_cols.end(), "$") == action_cols.end()) {
        action_cols.push_back("$");
    }
    std::vector<std::string> goto_cols;
    for (const auto& nt : non_terminal_symbols) {
        if (nt != START) {
            goto_cols.push_back(nt);
        }
    }
    const int W = 8;
    int action_total_w = action_cols.size() * W;
    int goto_total_w   = goto_cols.size() * W;
    auto print_h_line = [&]() {
        std::cout << "+-------+" << std::string(action_total_w, '-') << "+" << std::string(goto_total_w, '-') << "+\n";
    };
    std::cout << "\nSLR(1) Parsing Table:\n";
    print_h_line();
    std::cout << "| " << std::left << std::setw(5) << " " << " |"
              << std::setw(action_total_w / 2 + 3) << std::right << "ACTION"
              << std::setw(action_total_w - (action_total_w / 2 + 3)) << " " << "|"
              << std::setw(goto_total_w / 2 + 2) << std::right << "GOTO"
              << std::setw(goto_total_w - (goto_total_w / 2 + 2)) << " " << "|\n";
    std::cout << "| " << std::left << std::setw(5) << "State" << " |";
    for (const auto& term : action_cols) {
        std::cout << std::right << std::setw(W - 1) << term << " ";
    }
    std::cout << "|";
    for (const auto& non_term : goto_cols) {
        std::cout << std::right << std::setw(W - 1) << non_term << " ";
    }
    std::cout << "|\n";
    print_h_line();
    for (int i = 0; i < closure_slr1.size(); ++i) {
        std::cout << "| " << std::right << std::setw(5) << i << " |";
        for (const auto& term : action_cols) {
            std::string cell = "";
            if (analysis_table_slr1.count({i, term})) {
                auto act = analysis_table_slr1[{i, term}];
                if (act.first == SLRAction::S) {
                    cell = "s" + std::to_string(act.second);
                } else if (act.first == SLRAction::R) {
                    cell = "r" + std::to_string(act.second);
                } else if (act.first == SLRAction::Accept) {
                    cell = "acc";
                }
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|";
        for (const auto& non_term : goto_cols) {
            std::string cell = "";
            if (goto_slr1.count({i, non_term})) {
                cell = std::to_string(goto_slr1[{i, non_term}]);
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|\n";
    }
    print_h_line();
    std::cout << std::endl;
}
bool construct_slr1_analysis_table() {
    bool not_slr = false;
    for (auto edge:goto_slr1) {
        if (analysis_table_slr1.find({edge.first.first, edge.first.second}) != analysis_table_slr1.end()) {
            not_slr = true;
        }
        analysis_table_slr1[{edge.first.first, edge.first.second}] = {SLRAction::S, edge.second};
    }
    if (not_slr) {
        puts("This grammar does not belong to slr(1)\n");
        return false;
    }
    for (int i = 0; i < closure_slr1.size(); ++i) {
        for (auto production:closure_slr1[i].first) {
            if (production.back() == "\\cdot") {
                if (production.front() == START) {
                    analysis_table_slr1[{i, "$"}] = {SLRAction::Accept, -1};
                } else {
                    for (auto symbol:follow[production.front()]) {
                        if (analysis_table_slr1.find({i, symbol}) != analysis_table_slr1.end()) {
                            not_slr = true;
                        }
                        analysis_table_slr1[{i, symbol}] = {SLRAction::R, getindex(production)};
                    }
                }
            }
        }
    }
    if (not_slr) {
        puts("This grammar does not belong to slr(1)\n");
        return false;
    }
    print_slr_table();
    return true;
}
void analyse_slr1_sentence() {
    for (auto sentence : lr1sentence) {
        std::cout << "Analyse ";
        for (const auto &symbol : sentence) {
            std::cout << symbol << " ";
        }
        std::cout << ":\n";
        const int W_STEP   = 5;
        const int W_STATE  = 22;
        const int W_SYMBOL = 20;
        const int W_INPUT  = 20;
        std::cout << std::left 
                  << std::setw(W_STEP)   << "Step"   << " | "
                  << std::setw(W_STATE)  << "State"  << " | "
                  << std::setw(W_SYMBOL) << "Symbol" << " | "
                  << std::setw(W_INPUT)  << "Input"  << " | "
                  << "Action\n";
        std::cout << std::string(W_STEP, '-')   << "-+-"
                  << std::string(W_STATE, '-')  << "-+-"
                  << std::string(W_SYMBOL, '-') << "-+-"
                  << std::string(W_INPUT, '-')  << "-+-"
                  << "---------------------\n";
        int step = 0;
        int index = 0;
        std::stack<std::pair<int, std::string>> stack;
        stack.push({0, "$"});
        sentence.push_back("$");
        while (true) {
            step++;
            auto closure = stack.top().first;
            auto right_symbol = sentence[index];
            auto stack_copy = stack;
            auto action = analysis_table_slr1[{closure, right_symbol}].first;
            auto target = analysis_table_slr1[{closure, right_symbol}].second;
            auto _ = (action == SLRAction::R) ? getproduction(target) : std::pair<std::string, Production>{"", Production{}};
            auto left = _.first;
            auto production = _.second;
            std::vector<int> stack_items_first;
            std::vector<std::string> stack_items_second;
            while (!stack_copy.empty()) {
                stack_items_first.push_back(stack_copy.top().first);
                stack_items_second.push_back(stack_copy.top().second);
                stack_copy.pop();
            }
            std::ostringstream ss_state;
            for (auto it = stack_items_first.rbegin(); it != stack_items_first.rend(); ++it) {
                ss_state << *it << " ";
            }
            std::ostringstream ss_symbol;
            for (auto it = stack_items_second.rbegin(); it != stack_items_second.rend(); ++it) {
                ss_symbol << *it << " ";
            }
            std::ostringstream ss_input;
            for (int i = index; i < sentence.size(); ++i) {
                ss_input << sentence[i] << " ";
            }
            std::ostringstream ss_action;
            if (action == SLRAction::S) {
                ss_action << "Shift " << target;
            } else if (action == SLRAction::R) {
                ss_action << "Reduce: " << left << " → ";
                for (const auto& symbol : production) {
                    ss_action << symbol << " ";
                }
            } else if (action == SLRAction::Accept) {
                ss_action << "Accept";
            }
            std::cout << std::left
                      << std::setw(W_STEP)   << step            << " | "
                      << std::setw(W_STATE)  << ss_state.str()  << " | "
                      << std::setw(W_SYMBOL) << ss_symbol.str() << " | "
                      << std::setw(W_INPUT)  << ss_input.str()  << " | "
                      << ss_action.str() << "\n";
            if (action == SLRAction::Accept) {
                std::cout << "\n";
                break;
            }
            if (action == SLRAction::S) {
                stack.push({target, sentence[index++]});
            }
            if (action == SLRAction::R) {
                for (int i = 0; i < production.size(); ++i) {
                    stack.pop();
                }
                auto new_target = analysis_table_slr1[{stack.top().first, left}].second;
                stack.push({new_target, left});
            }
        }
    }
}
void export_to_dot_lr1(const std::string& filename = "./example/lr_dfa.dot") {
    std::ofstream out(filename);
    if (!out.is_open()) {
        std::cerr << "Failed to open " << filename << " for dot export.\n";
        return;
    }
    out << "digraph LR0_DFA {\n";
    out << "    rankdir=LR;\n";
    out << "    node [shape=box, fontname=\"Courier\", style=\"rounded,filled\", fillcolor=\"#f8f9fa\"];\n";
    out << "    edge [fontname=\"Courier\", fontsize=10];\n\n";
    for (int i = 0; i < closure_lr1.size(); ++i) {
        out << "    I" << i << " [shape=none, label=<\n";
        out << "        <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\" COLOR=\"#B0BEC5\">\n";
        out << "            <TR><TD BGCOLOR=\"#37474F\" ALIGN=\"CENTER\"><FONT COLOR=\"#FFFFFF\"><B>I<SUB>" 
            << i << "</SUB></B></FONT></TD></TR>\n";
        auto format_item_text = [](const Production& prod, const FollowSymbols& follow_symbols) {
            std::string text;
            for (auto symbol : prod) {
                if (symbol == "\\to") symbol = "-&gt;";
                else if (symbol == "\\cdot") symbol = "·";
                else if (symbol == "\\epsilon") symbol = "ε";
                else if (symbol == "<") symbol = "&lt;";
                else if (symbol == ">") symbol = "&gt;";
                else if (symbol == "&") symbol = "&amp;";
                text += symbol + " ";
            }
            text += ", ";
            for (auto symbol : follow_symbols) {
                if (symbol == "\\epsilon") symbol = "ε";
                else if (symbol == "<") symbol = "&lt;";
                else if (symbol == ">") symbol = "&gt;";
                else if (symbol == "&") symbol = "&amp;";
                text += symbol + " ";
            }
            return text;
        };
        for (const auto& prod : closure_lr1[i].first) {
            out << "            <TR><TD BGCOLOR=\"#E3F2FD\" ALIGN=\"LEFT\"><FONT COLOR=\"#0D47A1\"><B>"
                << format_item_text(prod.first, prod.second)
                << "</B></FONT></TD></TR>\n";
        }
        if (!closure_lr1[i].first.empty() && !closure_lr1[i].second.empty()) {
            out << "            <HR/>\n";
        }
        for (const auto& prod : closure_lr1[i].second) {
            out << "            <TR><TD BGCOLOR=\"#FAFAFA\" ALIGN=\"LEFT\"><FONT COLOR=\"#616161\">"
                << format_item_text(prod.first, prod.second)
                << "</FONT></TD></TR>\n";
        }
        out << "        </TABLE>\n";
        out << "    >];\n";
    }
    out << "\n";
    for (const auto& edge : goto_lr1) {
        int u = edge.first.first;
        std::string symbol = edge.first.second;
        int v = edge.second;
        if (symbol == "\\epsilon") symbol = "ε";
        if (symbol == "\"") symbol = "\\\"";
        out << "    I" << u << " -> I" << v << " [label=\"" << symbol << "\"];\n";
    }
    out << "}\n";
    out.close();
}
void construct_lr1_closure() {
    closure_lr1.push_back({{{{START, "\\to", "\\cdot", start_symbol}, {"$"}}}, {}});
    for (int i = 0;; ++i) {
        if (i >= closure_lr1.size()) break;
        std::unordered_map<std::string, std::vector<std::pair<Production, FollowSymbols>>> out_productions;
        for (auto production_follow_symbol:closure_lr1[i].first) {
            auto production = production_follow_symbol.first;
            auto follow_symbols = production_follow_symbol.second;
            auto cdot_position = std::find(production.begin(), production.end(), "\\cdot") - production.begin();
            if (cdot_position + 1 == production.size()) {
                continue;
            }
            auto symbol = production[cdot_position + 1];
            swap(production[cdot_position], production[cdot_position + 1]);
            FollowSymbols new_follow_symbols;
            bool need_follow_symbols = true;
            for (int k = cdot_position + 2; k < production.size(); ++k) {
                auto symbol = production[k];
                // 暂时没考虑 \\epsilon
                if (is_terminal_symbols(symbol)) {
                    new_follow_symbols.insert(symbol);
                    need_follow_symbols = false;
                    break;
                }
                if (is_non_terminal_symbols(symbol)) {
                    bool has_epsilon = false;
                    for (auto first_symbol:first[symbol]) {
                        if (first_symbol == "\\epsilon") {
                            has_epsilon = true;
                        } else {
                            new_follow_symbols.insert(first_symbol);
                        }
                    }
                    if (!has_epsilon) {
                        need_follow_symbols = false;
                        break;
                    }
                }
            }
            if (need_follow_symbols) {
                for (auto first_symbol:follow_symbols) {
                    new_follow_symbols.insert(first_symbol);
                }
            }
            if (is_non_terminal_symbols(symbol)) {
                for (auto production_right:productions[symbol]) {
                    Production s = {symbol, "\\to", "\\cdot"};
                    s.insert(s.end(), production_right.second.begin(), production_right.second.end());
                    bool prev_production_exist = false;
                    for (auto &temp_production_follow_symbol:closure_lr1[i].second) {
                        if (temp_production_follow_symbol.first == s) {
                            prev_production_exist = true;
                            for (auto sym:new_follow_symbols) {
                                temp_production_follow_symbol.second.insert(sym);
                            }
                        }
                    }
                    if (!prev_production_exist) {
                        closure_lr1[i].second.push_back({s, new_follow_symbols});
                    }
                }
            }
            out_productions[production[cdot_position]].push_back({production, follow_symbols});
        }
        for (int t = 0;; ++t) {
            if (t >= closure_lr1[i].second.size()) break;
            auto production_follow_symbol = closure_lr1[i].second[t];
            auto production = production_follow_symbol.first;
            auto follow_symbols = production_follow_symbol.second;
            auto cdot_position = std::find(production.begin(), production.end(), "\\cdot") - production.begin();
            if (cdot_position + 1 == production.size()) {
                continue;
            }
            auto symbol = production[cdot_position + 1];
            swap(production[cdot_position], production[cdot_position + 1]);
            FollowSymbols new_follow_symbols;
            bool need_follow_symbols = true;
            for (int k = cdot_position + 2; k < production.size(); ++k) {
                auto symbol = production[k];
                // 暂时没考虑 \\epsilon
                if (is_terminal_symbols(symbol)) {
                    new_follow_symbols.insert(symbol);
                    need_follow_symbols = false;
                    break;
                }
                if (is_non_terminal_symbols(symbol)) {
                    bool has_epsilon = false;
                    for (auto first_symbol:first[symbol]) {
                        if (first_symbol == "\\epsilon") {
                            has_epsilon = true;
                        } else {
                            new_follow_symbols.insert(first_symbol);
                        }
                    }
                    if (!has_epsilon) {
                        need_follow_symbols = false;
                        break;
                    }
                }
            }
            if (need_follow_symbols) {
                for (auto first_symbol:follow_symbols) {
                    new_follow_symbols.insert(first_symbol);
                }
            }
            if (is_non_terminal_symbols(symbol)) {
                for (auto production_right:productions[symbol]) {
                    Production s = {symbol, "\\to", "\\cdot"};
                    s.insert(s.end(), production_right.second.begin(), production_right.second.end());
                    bool prev_production_exist = false;
                    for (auto &temp_production_follow_symbol:closure_lr1[i].second) {
                        if (temp_production_follow_symbol.first == s) {
                            prev_production_exist = true;
                            for (auto sym:new_follow_symbols) {
                                temp_production_follow_symbol.second.insert(sym);
                            }
                        }
                    }
                    if (!prev_production_exist) {
                        closure_lr1[i].second.push_back({s, new_follow_symbols});
                    }
                }
            }
        }
        for (auto production_follow_symbol:closure_lr1[i].second) {
            auto production = production_follow_symbol.first;
            auto follow_symbols = production_follow_symbol.second;
            auto cdot_position = std::find(production.begin(), production.end(), "\\cdot") - production.begin();
            std::swap(production[cdot_position], production[cdot_position + 1]);
            out_productions[production[cdot_position]].push_back({production, follow_symbols});
        }
        for (auto symbol:terminal_symbols) {
            if (out_productions[symbol].empty()) {
                continue;
            }
            bool prev_exist = false;
            for (int closure_index = 0; closure_index < closure_lr1.size(); ++closure_index) {
                const auto &closure = closure_lr1[closure_index];
                bool found = !out_productions[symbol].empty() && closure.first.size() == out_productions[symbol].size();
                if (found) {
                    for (const auto &production:closure.first) {
                        if (std::find(out_productions[symbol].begin(), out_productions[symbol].end(), production) == out_productions[symbol].end()) {
                            found = false;
                            break;
                        }
                    }
                }
                if (found) {
                    goto_lr1[{i, symbol}] = closure_index;
                    prev_exist = true;
                    break;
                }
            }
            if (!prev_exist) {
                goto_lr1[{i, symbol}] = closure_lr1.size();
                closure_lr1.push_back({out_productions[symbol], {}});
            }
        }
        for (auto symbol:non_terminal_symbols) {
            if (out_productions[symbol].empty()) {
                continue;
            }
            bool prev_exist = false;
            for (int closure_index = 0; closure_index < closure_lr1.size(); ++closure_index) {
                const auto &closure = closure_lr1[closure_index];
                bool found = !out_productions[symbol].empty() && closure.first.size() == out_productions[symbol].size();
                if (found) {
                    for (const auto &production:closure.first) {
                        if (std::find(out_productions[symbol].begin(), out_productions[symbol].end(), production) == out_productions[symbol].end()) {
                            found = false;
                            break;
                        }
                    }
                }
                if (found) {
                    goto_lr1[{i, symbol}] = closure_index;
                    prev_exist = true;
                    break;
                }
            }
            if (!prev_exist) {
                goto_lr1[{i, symbol}] = closure_lr1.size();
                closure_lr1.push_back({out_productions[symbol], {}});
            }
        }
    }
    export_to_dot_lr1();
}
void print_lr1_table() {
    std::vector<std::string> action_cols = terminal_symbols;
    if (std::find(action_cols.begin(), action_cols.end(), "$") == action_cols.end()) {
        action_cols.push_back("$");
    }
    std::vector<std::string> goto_cols;
    for (const auto& nt : non_terminal_symbols) {
        if (nt != START) {
            goto_cols.push_back(nt);
        }
    }
    const int W = 8;
    int action_total_w = action_cols.size() * W;
    int goto_total_w   = goto_cols.size() * W;
    auto print_h_line = [&]() {
        std::cout << "+-------+" << std::string(action_total_w, '-') << "+" << std::string(goto_total_w, '-') << "+\n";
    };
    std::cout << "\nLR(1) Parsing Table:\n";
    print_h_line();
    std::cout << "| " << std::left << std::setw(5) << " " << " |"
              << std::setw(action_total_w / 2 + 3) << std::right << "ACTION"
              << std::setw(action_total_w - (action_total_w / 2 + 3)) << " " << "|"
              << std::setw(goto_total_w / 2 + 2) << std::right << "GOTO"
              << std::setw(goto_total_w - (goto_total_w / 2 + 2)) << " " << "|\n";
    std::cout << "| " << std::left << std::setw(5) << "State" << " |";
    for (const auto& term : action_cols) {
        std::cout << std::right << std::setw(W - 1) << term << " ";
    }
    std::cout << "|";
    for (const auto& non_term : goto_cols) {
        std::cout << std::right << std::setw(W - 1) << non_term << " ";
    }
    std::cout << "|\n";
    print_h_line();
    for (int i = 0; i < closure_lr1.size(); ++i) {
        std::cout << "| " << std::right << std::setw(5) << i << " |";
        for (const auto& term : action_cols) {
            std::string cell = "";
            if (analysis_table_lr1.count({i, term})) {
                auto act = analysis_table_lr1[{i, term}];
                if (act.first == SLRAction::S) {
                    cell = "s" + std::to_string(act.second);
                } else if (act.first == SLRAction::R) {
                    cell = "r" + std::to_string(act.second);
                } else if (act.first == SLRAction::Accept) {
                    cell = "acc";
                }
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|";
        for (const auto& non_term : goto_cols) {
            std::string cell = "";
            if (goto_lr1.count({i, non_term})) {
                cell = std::to_string(goto_lr1[{i, non_term}]);
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|\n";
    }
    print_h_line();
    std::cout << std::endl;
}
void construct_lr1_analysis_table() {
    for (auto edge:goto_lr1) {
        analysis_table_lr1[{edge.first.first, edge.first.second}] = {SLRAction::S, edge.second};
    }
    for (int i = 0; i < closure_lr1.size(); ++i) {
        for (auto production_follow_symbols:closure_lr1[i].first) {
            auto production = production_follow_symbols.first;
            auto follow_symbols = production_follow_symbols.second;
            if (production.back() == "\\cdot") {
                if (production.front() == START) {
                    analysis_table_lr1[{i, "$"}] = {SLRAction::Accept, -1};
                } else {
                    for (auto symbol:follow_symbols) {
                        if (analysis_table_lr1.find({i, symbol}) != analysis_table_lr1.end()) {
                        }
                        analysis_table_lr1[{i, symbol}] = {SLRAction::R, getindex(production)};
                    }
                }
            }
        }
    }
    print_lr1_table();
}
void analyse_lr1_sentence() {
    for (auto sentence : lr1sentence) {
        std::cout << "Analyse ";
        for (const auto &symbol : sentence) {
            std::cout << symbol << " ";
        }
        std::cout << ":\n";
        const int W_STEP   = 5;
        const int W_STATE  = 22;
        const int W_SYMBOL = 20;
        const int W_INPUT  = 20;
        std::cout << std::left 
                  << std::setw(W_STEP)   << "Step"   << " | "
                  << std::setw(W_STATE)  << "State"  << " | "
                  << std::setw(W_SYMBOL) << "Symbol" << " | "
                  << std::setw(W_INPUT)  << "Input"  << " | "
                  << "Action\n";
        std::cout << std::string(W_STEP, '-')   << "-+-"
                  << std::string(W_STATE, '-')  << "-+-"
                  << std::string(W_SYMBOL, '-') << "-+-"
                  << std::string(W_INPUT, '-')  << "-+-"
                  << "---------------------\n";
        int step = 0;
        int index = 0;
        std::stack<std::pair<int, std::string>> stack;
        stack.push({0, "$"});
        sentence.push_back("$");
        while (true) {
            step++;
            auto closure = stack.top().first;
            auto right_symbol = sentence[index];
            auto stack_copy = stack;
            auto action = analysis_table_lr1[{closure, right_symbol}].first;
            auto target = analysis_table_lr1[{closure, right_symbol}].second;
            auto _ = (action == SLRAction::R) ? getproduction(target) : std::pair<std::string, Production>{"", Production{}};
            auto left = _.first;
            auto production = _.second;
            std::vector<int> stack_items_first;
            std::vector<std::string> stack_items_second;
            while (!stack_copy.empty()) {
                stack_items_first.push_back(stack_copy.top().first);
                stack_items_second.push_back(stack_copy.top().second);
                stack_copy.pop();
            }
            std::ostringstream ss_state;
            for (auto it = stack_items_first.rbegin(); it != stack_items_first.rend(); ++it) {
                ss_state << *it << " ";
            }
            std::ostringstream ss_symbol;
            for (auto it = stack_items_second.rbegin(); it != stack_items_second.rend(); ++it) {
                ss_symbol << *it << " ";
            }
            std::ostringstream ss_input;
            for (int i = index; i < sentence.size(); ++i) {
                ss_input << sentence[i] << " ";
            }
            std::ostringstream ss_action;
            if (action == SLRAction::S) {
                ss_action << "Shift " << target;
            } else if (action == SLRAction::R) {
                ss_action << "Reduce: " << left << " → ";
                for (const auto& symbol : production) {
                    ss_action << symbol << " ";
                }
            } else if (action == SLRAction::Accept) {
                ss_action << "Accept";
            }
            std::cout << std::left
                      << std::setw(W_STEP)   << step            << " | "
                      << std::setw(W_STATE)  << ss_state.str()  << " | "
                      << std::setw(W_SYMBOL) << ss_symbol.str() << " | "
                      << std::setw(W_INPUT)  << ss_input.str()  << " | "
                      << ss_action.str() << "\n";
            if (action == SLRAction::Accept) {
                std::cout << "\n";
                break;
            }
            if (action == SLRAction::S) {
                stack.push({target, sentence[index++]});
            }
            if (action == SLRAction::R) {
                for (int i = 0; i < production.size(); ++i) {
                    stack.pop();
                }
                auto new_target = analysis_table_lr1[{stack.top().first, left}].second;
                stack.push({new_target, left});
            }
        }
    }
}
void export_to_dot_lalr1(const std::string& filename = "./example/lalr_dfa.dot") {
    std::ofstream out(filename);
    if (!out.is_open()) {
        std::cerr << "Failed to open " << filename << " for dot export.\n";
        return;
    }
    out << "digraph LR0_DFA {\n";
    out << "    rankdir=LR;\n";
    out << "    node [shape=box, fontname=\"Courier\", style=\"rounded,filled\", fillcolor=\"#f8f9fa\"];\n";
    out << "    edge [fontname=\"Courier\", fontsize=10];\n\n";
    for (int i = 0; i < closure_lalr1.size(); ++i) {
        out << "    I" << i << " [shape=none, label=<\n";
        out << "        <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\" COLOR=\"#B0BEC5\">\n";
        out << "            <TR><TD BGCOLOR=\"#37474F\" ALIGN=\"CENTER\"><FONT COLOR=\"#FFFFFF\"><B>I<SUB>" 
            << i << "</SUB></B></FONT></TD></TR>\n";
        auto format_item_text = [](const Production& prod, const FollowSymbols& follow_symbols) {
            std::string text;
            for (auto symbol : prod) {
                if (symbol == "\\to") symbol = "-&gt;";
                else if (symbol == "\\cdot") symbol = "·";
                else if (symbol == "\\epsilon") symbol = "ε";
                else if (symbol == "<") symbol = "&lt;";
                else if (symbol == ">") symbol = "&gt;";
                else if (symbol == "&") symbol = "&amp;";
                text += symbol + " ";
            }
            text += ", ";
            for (auto symbol : follow_symbols) {
                if (symbol == "\\epsilon") symbol = "ε";
                else if (symbol == "<") symbol = "&lt;";
                else if (symbol == ">") symbol = "&gt;";
                else if (symbol == "&") symbol = "&amp;";
                text += symbol + " ";
            }
            return text;
        };
        for (const auto& prod : closure_lalr1[i].first) {
            out << "            <TR><TD BGCOLOR=\"#E3F2FD\" ALIGN=\"LEFT\"><FONT COLOR=\"#0D47A1\"><B>"
                << format_item_text(prod.first, prod.second)
                << "</B></FONT></TD></TR>\n";
        }
        if (!closure_lalr1[i].first.empty() && !closure_lalr1[i].second.empty()) {
            out << "            <HR/>\n";
        }
        for (const auto& prod : closure_lalr1[i].second) {
            out << "            <TR><TD BGCOLOR=\"#FAFAFA\" ALIGN=\"LEFT\"><FONT COLOR=\"#616161\">"
                << format_item_text(prod.first, prod.second)
                << "</FONT></TD></TR>\n";
        }
        out << "        </TABLE>\n";
        out << "    >];\n";
    }
    out << "\n";
    for (const auto& edge : goto_lalr1) {
        int u = edge.first.first;
        std::string symbol = edge.first.second;
        int v = edge.second;
        if (symbol == "\\epsilon") symbol = "ε";
        if (symbol == "\"") symbol = "\\\"";
        out << "    I" << u << " -> I" << v << " [label=\"" << symbol << "\"];\n";
    }
    out << "}\n";
    out.close();
}
void construct_lalr1_closure() {
    closure_lalr1 = closure_lr1;
    goto_lalr1 = goto_lr1;
    int n = closure_lalr1.size();
    if (n == 0) return;
    auto is_same_core = [](const std::vector<std::pair<Production, FollowSymbols>>& k1, const std::vector<std::pair<Production, FollowSymbols>>& k2) -> bool {
        if (k1.size() != k2.size()) return false;
        std::vector<bool> matched(k2.size(), false);
        for (const auto& item1 : k1) {
            bool found = false;
            for (size_t idx = 0; idx < k2.size(); ++idx) {
                if (!matched[idx] && item1.first == k2[idx].first) {
                    matched[idx] = true;
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
        return true;
    };
    std::vector<int> old_to_new(n, -1);
    std::vector<std::vector<int>> groups;
    for (int i = 0; i < n; ++i) {
        if (old_to_new[i] != -1) continue;
        int new_id = groups.size();
        groups.push_back({i});
        old_to_new[i] = new_id;
        for (int j = i + 1; j < n; ++j) {
            if (old_to_new[j] == -1 && is_same_core(closure_lalr1[i].first, closure_lalr1[j].first)) {
                groups[new_id].push_back(j);
                old_to_new[j] = new_id;
            }
        }
    }
    auto merge_items = [](const std::vector<int>& group,
                          const std::vector<std::pair<std::vector<std::pair<Production, FollowSymbols>>, std::vector<std::pair<Production, FollowSymbols>>>>& old_states,
                          bool is_kernel) -> std::vector<std::pair<Production, FollowSymbols>> {
        std::vector<std::pair<Production, FollowSymbols>> merged;
        for (int old_idx : group) {
            const auto& items = is_kernel ? old_states[old_idx].first : old_states[old_idx].second;
            for (const auto& item : items) {
                const auto& prod = item.first;
                const auto& lookaheads = item.second;

                auto it = std::find_if(merged.begin(), merged.end(),
                    [&](const std::pair<Production, FollowSymbols>& existing) { return existing.first == prod; });

                if (it != merged.end()) {
                    it->second.insert(lookaheads.begin(), lookaheads.end());
                } else {
                    merged.push_back({prod, lookaheads});
                }
            }
        }
        return merged;
    };
    std::vector<std::pair<std::vector<std::pair<Production, FollowSymbols>>, std::vector<std::pair<Production, FollowSymbols>>>> new_closure_lalr1;
    new_closure_lalr1.reserve(groups.size());
    for (const auto& group : groups) {
        std::vector<std::pair<Production, FollowSymbols>> merged_kernel = merge_items(group, closure_lalr1, true);
        std::vector<std::pair<Production, FollowSymbols>> merged_non_kernel = merge_items(group, closure_lalr1, false);
        new_closure_lalr1.push_back({merged_kernel, merged_non_kernel});
    }
    std::map<std::pair<int, std::string>, int> new_goto_lalr1;
    for (const auto& entry : goto_lalr1) {
        int old_from = entry.first.first;
        const std::string& symbol = entry.first.second;
        int old_to = entry.second;
        int new_from = old_to_new[old_from];
        int new_to = old_to_new[old_to];
        new_goto_lalr1[{new_from, symbol}] = new_to;
    }
    closure_lalr1 = std::move(new_closure_lalr1);
    goto_lalr1 = std::move(new_goto_lalr1);
    export_to_dot_lalr1();
}
void print_lalr1_table() {
    std::vector<std::string> action_cols = terminal_symbols;
    if (std::find(action_cols.begin(), action_cols.end(), "$") == action_cols.end()) {
        action_cols.push_back("$");
    }
    std::vector<std::string> goto_cols;
    for (const auto& nt : non_terminal_symbols) {
        if (nt != START) {
            goto_cols.push_back(nt);
        }
    }
    const int W = 8;
    int action_total_w = action_cols.size() * W;
    int goto_total_w   = goto_cols.size() * W;
    auto print_h_line = [&]() {
        std::cout << "+-------+" << std::string(action_total_w, '-') << "+" << std::string(goto_total_w, '-') << "+\n";
    };
    std::cout << "\nLALR(1) Parsing Table:\n";
    print_h_line();
    std::cout << "| " << std::left << std::setw(5) << " " << " |"
              << std::setw(action_total_w / 2 + 3) << std::right << "ACTION"
              << std::setw(action_total_w - (action_total_w / 2 + 3)) << " " << "|"
              << std::setw(goto_total_w / 2 + 2) << std::right << "GOTO"
              << std::setw(goto_total_w - (goto_total_w / 2 + 2)) << " " << "|\n";
    std::cout << "| " << std::left << std::setw(5) << "State" << " |";
    for (const auto& term : action_cols) {
        std::cout << std::right << std::setw(W - 1) << term << " ";
    }
    std::cout << "|";
    for (const auto& non_term : goto_cols) {
        std::cout << std::right << std::setw(W - 1) << non_term << " ";
    }
    std::cout << "|\n";
    print_h_line();
    for (int i = 0; i < closure_lalr1.size(); ++i) {
        std::cout << "| " << std::right << std::setw(5) << i << " |";
        for (const auto& term : action_cols) {
            std::string cell = "";
            if (analysis_table_lr1.count({i, term})) {
                auto act = analysis_table_lr1[{i, term}];
                if (act.first == SLRAction::S) {
                    cell = "s" + std::to_string(act.second);
                } else if (act.first == SLRAction::R) {
                    cell = "r" + std::to_string(act.second);
                } else if (act.first == SLRAction::Accept) {
                    cell = "acc";
                }
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|";
        for (const auto& non_term : goto_cols) {
            std::string cell = "";
            if (goto_lalr1.count({i, non_term})) {
                cell = std::to_string(goto_lalr1[{i, non_term}]);
            }
            std::cout << std::right << std::setw(W - 1) << cell << " ";
        }
        std::cout << "|\n";
    }
    print_h_line();
    std::cout << std::endl;
}
void construct_lalr1_analysis_table() {
    for (auto edge:goto_lalr1) {
        analysis_table_lalr1[{edge.first.first, edge.first.second}] = {SLRAction::S, edge.second};
    }
    for (int i = 0; i < closure_lalr1.size(); ++i) {
        for (auto production_follow_symbols:closure_lalr1[i].first) {
            auto production = production_follow_symbols.first;
            auto follow_symbols = production_follow_symbols.second;
            if (production.back() == "\\cdot") {
                if (production.front() == START) {
                    analysis_table_lalr1[{i, "$"}] = {SLRAction::Accept, -1};
                } else {
                    for (auto symbol:follow_symbols) {
                        if (analysis_table_lalr1.find({i, symbol}) != analysis_table_lalr1.end()) {
                        }
                        analysis_table_lalr1[{i, symbol}] = {SLRAction::R, getindex(production)};
                    }
                }
            }
        }
    }
    print_lalr1_table();
}
void analyse_lalr1_sentence() {
    for (auto sentence : lr1sentence) {
        std::cout << "Analyse ";
        for (const auto &symbol : sentence) {
            std::cout << symbol << " ";
        }
        std::cout << ":\n";
        const int W_STEP   = 5;
        const int W_STATE  = 22;
        const int W_SYMBOL = 20;
        const int W_INPUT  = 20;
        std::cout << std::left 
                  << std::setw(W_STEP)   << "Step"   << " | "
                  << std::setw(W_STATE)  << "State"  << " | "
                  << std::setw(W_SYMBOL) << "Symbol" << " | "
                  << std::setw(W_INPUT)  << "Input"  << " | "
                  << "Action\n";
        std::cout << std::string(W_STEP, '-')   << "-+-"
                  << std::string(W_STATE, '-')  << "-+-"
                  << std::string(W_SYMBOL, '-') << "-+-"
                  << std::string(W_INPUT, '-')  << "-+-"
                  << "---------------------\n";
        int step = 0;
        int index = 0;
        std::stack<std::pair<int, std::string>> stack;
        stack.push({0, "$"});
        sentence.push_back("$");
        while (true) {
            step++;
            auto closure = stack.top().first;
            auto right_symbol = sentence[index];
            auto stack_copy = stack;
            auto action = analysis_table_lalr1[{closure, right_symbol}].first;
            auto target = analysis_table_lalr1[{closure, right_symbol}].second;
            auto _ = (action == SLRAction::R) ? getproduction(target) : std::pair<std::string, Production>{"", Production{}};
            auto left = _.first;
            auto production = _.second;
            std::vector<int> stack_items_first;
            std::vector<std::string> stack_items_second;
            while (!stack_copy.empty()) {
                stack_items_first.push_back(stack_copy.top().first);
                stack_items_second.push_back(stack_copy.top().second);
                stack_copy.pop();
            }
            std::ostringstream ss_state;
            for (auto it = stack_items_first.rbegin(); it != stack_items_first.rend(); ++it) {
                ss_state << *it << " ";
            }
            std::ostringstream ss_symbol;
            for (auto it = stack_items_second.rbegin(); it != stack_items_second.rend(); ++it) {
                ss_symbol << *it << " ";
            }
            std::ostringstream ss_input;
            for (int i = index; i < sentence.size(); ++i) {
                ss_input << sentence[i] << " ";
            }
            std::ostringstream ss_action;
            if (action == SLRAction::S) {
                ss_action << "Shift " << target;
            } else if (action == SLRAction::R) {
                ss_action << "Reduce: " << left << " → ";
                for (const auto& symbol : production) {
                    ss_action << symbol << " ";
                }
            } else if (action == SLRAction::Accept) {
                ss_action << "Accept";
            }
            std::cout << std::left
                      << std::setw(W_STEP)   << step            << " | "
                      << std::setw(W_STATE)  << ss_state.str()  << " | "
                      << std::setw(W_SYMBOL) << ss_symbol.str() << " | "
                      << std::setw(W_INPUT)  << ss_input.str()  << " | "
                      << ss_action.str() << "\n";
            if (action == SLRAction::Accept) {
                std::cout << "\n";
                break;
            }
            if (action == SLRAction::S) {
                stack.push({target, sentence[index++]});
            }
            if (action == SLRAction::R) {
                for (int i = 0; i < production.size(); ++i) {
                    stack.pop();
                }
                auto new_target = analysis_table_lalr1[{stack.top().first, left}].second;
                stack.push({new_target, left});
            }
        }
    }
}
void solve_left_recursion() {
    std::vector<std::string> new_symbols;
    for (auto non_terminal_symbol:non_terminal_symbols) {
        auto left_index = std::distance(non_terminal_symbols.begin(), std::find(non_terminal_symbols.begin(), non_terminal_symbols.end(), non_terminal_symbol));
        std::vector<Recursion> happen_recrusion;
        bool allow_recrusion = false;
        for (int i = 0; i < productions[non_terminal_symbol].size(); ++i) {
            auto production = productions[non_terminal_symbol][i];
            auto symbol = production.second[0];
            if (is_terminal_symbols(symbol)) {
                happen_recrusion.push_back(Recursion::False);
                continue;
            }
            auto right_index = std::distance(non_terminal_symbols.begin(), std::find(non_terminal_symbols.begin(), non_terminal_symbols.end(), symbol));
            if (right_index < left_index) {
                auto right_symbol = non_terminal_symbols[right_index];
                bool the_first_production = true;
                for (auto right_production:productions[right_symbol]) {
                    Production temp;
                    for (auto s:right_production.second) {
                        temp.push_back(s);
                    }
                    for (int j = 1; j < production.second.size(); ++j) {
                        temp.push_back(production.second[j]);
                    }
                    if (the_first_production) {
                        productions[non_terminal_symbol].push_back({right_production.first, temp});
                        happen_recrusion.push_back(Recursion::Replace);
                        the_first_production = false;
                    } else {
                        productions[non_terminal_symbol].push_back({++production_index, temp});
                    }
                }
            }
            if (right_index == left_index) {
                happen_recrusion.push_back(Recursion::True);
                allow_recrusion = true;
            }
            if (right_index > left_index) {
                happen_recrusion.push_back(Recursion::False);
            }
        }
        auto new_symbol = non_terminal_symbol + "-EXTERNAL";
        if (allow_recrusion) {
            new_symbols.push_back(new_symbol);
            std::vector<std::pair<int, Production>> to_change_production;
            for (int i = 0; i < happen_recrusion.size(); ++i) {
                if (happen_recrusion[i] == Recursion::True) {
                    auto index = productions[non_terminal_symbol][i].first;
                    auto production = productions[non_terminal_symbol][i].second;
                    Production temp;
                    for (int j = 1; j < production.size(); ++j) {
                        temp.push_back(production[j]);
                    }
                    temp.push_back(new_symbol);
                    productions[new_symbol].push_back({index, temp});
                }
                if (happen_recrusion[i] == Recursion::False) {
                    to_change_production.push_back(productions[non_terminal_symbol][i]);
                    to_change_production[to_change_production.size() - 1].second.push_back(new_symbol);
                }
            }
            productions[non_terminal_symbol].clear();
            for (const auto &production:to_change_production) {
                productions[non_terminal_symbol].push_back(production);
            }
            productions[new_symbol].push_back({++production_index, {"\\epsilon"}});
            symbols[new_symbol] = Symbol::Non_TerminalSymbol;
            can_be_epsilon[new_symbol] = Epsilon::No;
            non_terminal_symbols.push_back(new_symbol);
        }
    }
    puts("After solve left recursion:");
    for (const auto &non_terminal_symbol:non_terminal_symbols) {
        for (const auto &production:productions[non_terminal_symbol]) {
            std::cout << non_terminal_symbol << " → ";
            for (const auto &symbol:production.second) {
                auto output = symbol;
                if (output == "\\epsilon") output = "ε";
                std::cout << output << " ";
            }
            puts("");
        }
    }
    puts("");
}
int main() {
    freopen("./example/1.larry", "r", stdin);
    freopen("./example/1.yrral", "w", stdout);
    if (!initial()) {
        return 0;
    }
    confirm_epsilon();
    if (enable_solve_left_recursion) {
        solve_left_recursion();
    }
    if (getfirst()) {
        puts("This grammar belongs to left recursion grammar");
    }
    getfollow();
    if (checkLL1()) {
        puts("This grammar belongs to LL(1).");
        construct_predict_table();
        analyse_ll1_sentence();
    } else {
        puts("This grammar does not belong to LL(1).");
    }
    argumentation_grammar();
    construct_slr1_closure();
    if (construct_slr1_analysis_table()) {
        analyse_slr1_sentence();
    }
    construct_lr1_closure();
    construct_lr1_analysis_table();
    analyse_lr1_sentence();
    construct_lalr1_closure();
    construct_lalr1_analysis_table();
    analyse_lalr1_sentence();
    return 0;
}
