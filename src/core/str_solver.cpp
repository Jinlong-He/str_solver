#include <fstream>
#include "str_solver.hpp"
void StrSolver::parseIdcras(const strings& strs, IDCRAs& idcras) {
    strings idcraStrs;
    for (auto& str : strs) {
        if (str.find("#automata:") != string::npos) {
            idcraStrs.clear();
            continue;
        }
        if (str.find("#end") != string::npos) {
            IDCRA* idcra = new IDCRA();
            IdcraParser::parse(idcraStrs, *idcra);
            //atl::print_automaton(*idcra);
            //cout << endl;
            idcras.push_back(idcra);
            continue;
        }
        idcraStrs.push_back(str);
    }
}

void StrSolver::parseIdcrasList(const strings& strs) {
    strings idcrasStrs;
    bool flag = true;
    for (auto& str : strs) {
        if (str.find("$") != string::npos && flag) {
            idcrasStrs.clear();
            flag = false;
            continue;
        }
        if (str.find("$") != string::npos && !flag) {
            IDCRAs idcras;
            parseIdcras(idcrasStrs, idcras);
            idcrasList_.push_back(idcras);
            flag = true;
            continue;
        }
        idcrasStrs.push_back(str);
    }
}

void StrSolver::parseConstrain(const string& str) {
    fomula_ = ll::propositional_fomula(str.substr(0, str.find_last_of("E") + 1));
}

void StrSolver::parseDeclaration(const string& str) {
    ID pos = str.find_first_of("(") + 1,
           length = str.find_first_of(")") - pos;
    if (length > 0) {
        boost::split(undeclaredVar_, str.substr(pos, length), boost::is_any_of(","));
    }
}

void StrSolver::parse(const strings& strs) {
    parseDeclaration(strs[0]);
    parseConstrain(strs[2]);
    parseIdcrasList(strings(strs.begin() + 3, strs.end()));
}

void StrSolver::readFile(const string& fileName, strings& strs) {
    std::fstream fs;
    fs.open (fileName, std::fstream::in);
    if (fs.is_open()) {
        string str;
        while(getline(fs, str)) {
            strs.push_back(str);
        }
        fs.close();
    }
}

void StrSolver::getCounterIdcrasList() {
    std::set<int> labelNodes;
    for (auto& idcras : idcrasList_) {
        for (auto idcra : idcras) {
            for (auto& l : alphabet(*idcra)) {
                labelNodes.insert(l.min());
                labelNodes.insert(l.max() + 1);
            }
        }
        IDCRAs newIdcras;
        for (auto idcra : idcras) {
            IDCRA* newIdcra = new IDCRA();
            atl::set_property(*newIdcra, atl::get_property(*idcra));
            typename IDCRA::StateIter it, end;
            typename IDCRA::TransitionIter tit, tend;
            for (tie(it, end) = states(*idcra); it != end; it++) {
                add_state(*newIdcra);
                if (is_final_state(*idcra, *it)) {
                    newIdcra -> set_final_state(*it);
                }
                if (idcra -> initial_state() == *it) {
                    newIdcra -> set_initial_state(*it);
                }
            }
            for (tie(tit, tend) = transitions(*idcra); tit != tend; tit++) {
                const auto& p = atl::get_property(*idcra, *tit);
                auto setIt = labelNodes.find(p.symbol.min());
                auto nextIt = setIt;
                nextIt++;
                while (nextIt != labelNodes.end() && *nextIt <= p.symbol.max() + 1) {
                    Label l(*setIt++, (*nextIt++) - 1);
                    add_transition(*newIdcra, 
                                   atl::source(*idcra, *tit), atl::target(*idcra, *tit),
                                   l, p.symbol_property);
                    set_alphabet(*newIdcra, l);
                }
            }
            newIdcras.push_back(newIdcra);
        }
        counterIdcrasList_.push_back(newIdcras);
    }
}

void toNRA(IDCRA& idcra, NRA& nra) {
    typename IDCRA::StateIter it, end;
    atl::set_property(nra, atl::get_property(idcra));
    for (tie(it, end) = states(idcra); it != end; it++) {
        auto state = add_state(nra);
        if (*it == idcra.initial_state()) set_initial_state(nra, state);
        if (is_final_state(idcra, *it)) set_final_state(nra, state);
    }
    for (tie(it, end) = states(idcra); it != end; it++) {
        typename IDCRA::OutTransitionIter tit, tend;
        for (tie(tit, tend) = out_transitions(idcra, *it); tit != tend; tit++) {
            const auto& p = atl::get_property(idcra, *tit).symbol_property;
            add_transition(nra, *it, atl::target(idcra, *tit), p);
            set_alphabet(nra, p);
        }
    }
}

DFA toDFA(IDCRA& idcra, typename IDCRA::State2StateSetMap& h_map,
          unordered_map<typename IDCRA::StatePair, unordered_map<Label, vector<Registers> > >& r_map) {
    NFA nfa;
    typename IDCRA::StateIter it, end;
    for (tie(it, end) = states(idcra); it != end; it++) {
        auto state = add_state(nfa);
        if (*it == idcra.initial_state()) set_initial_state(nfa, state);
        if (is_final_state(idcra, *it)) set_final_state(nfa, state);
    }
    for (tie(it, end) = states(idcra); it != end; it++) {
        typename IDCRA::OutTransitionIter tit, tend;
        for (tie(tit, tend) = out_transitions(idcra, *it); tit != tend; tit++) {
            typename IDCRA::State s = *it, t = atl::target(idcra, *tit);
            auto& trans = atl::get_property(idcra, *tit);
            auto& c = trans.symbol;
            auto& p = trans.symbol_property;
            add_transition(nfa, s, t, c);
            r_map[typename IDCRA::StatePair(s, t)][c].push_back(p);
        }
    }
    return (minimize(nfa, h_map));
}

void StrSolver::solve1(const string& timeout) {
    typedef typename IDCRA::State State;
    typedef typename IDCRA::StatePair StatePair;
    typedef typename IDCRA::StateSet StateSet;
    fa_ = new fomula_automaton();
    for (auto& var : undeclaredVar_) {
        add_input_state(*fa_, int_variable(var));
    }
    ID i = 0;
    auto f = fomula_;
    for (auto& idcras : counterIdcrasList_) {
        vector<typename IDCRA::State2StateSetMap> h_maps;
        vector<unordered_map<StatePair, unordered_map<Label, vector<Registers> > > > r_maps;
        unordered_map<State, vector<vector<State> > > intersect_map;
        typename IDCRA::State2StateSetMap h_map;
        unordered_map<StatePair, unordered_map<Label, vector<Registers> > > r_map;
        DFA res = toDFA(*(idcras.front()), h_map, r_map);
        h_maps.push_back(h_map);
        r_maps.push_back(r_map);
        //print_fa(res);
        for (auto fa : idcras) {
            if (fa == idcras.front()) continue;
            cout << "*******start intersect********" << endl;
            typename IDCRA::State2StateSetMap h_map;
            unordered_map<StatePair, unordered_map<Label, vector<Registers> > > r_map;
            DFA dfa = toDFA(*fa, h_map, r_map);
            h_maps.push_back(h_map);
            r_maps.push_back(r_map);
            typename IDCRA::State2StatePairsMap hp_map;
            //cout << "===========" << endl;
            //print_fa(dfa);
            res = get_intersect_fa(res, dfa, hp_map);
            if (intersect_map.size() == 0) {
                for (auto& map_pair : hp_map) {
                    auto& vecs = intersect_map[map_pair.first];
                    for (auto& s_pair : map_pair.second) {
                        vector<State> vec({s_pair.first, s_pair.second});
                        vecs.push_back(vec);
                    }
                }
            } else {
                unordered_map<State, vector<vector<State> > > new_intersect_map;
                for (auto& map_pair : hp_map) {
                    auto& new_vecs = new_intersect_map[map_pair.first];
                    for (auto& s_pair : map_pair.second) {
                        auto& vecs = intersect_map.at(s_pair.first);
                        for (auto& vec : vecs) {
                            vector<State> new_vec(vec);
                            new_vec.push_back(s_pair.second);
                            new_vecs.push_back(new_vec);
                        }
                    }
                }
                intersect_map.clear();
                intersect_map = new_intersect_map;
            }
            //print_fa(res);
            cout << "*******end intersect********" << endl;
        }

        if (is_empty(res)) {
            cout << "intersection is empty, this is true !" << endl;
            return;
        }
        cout << "finish intersection" << endl;
        print_fa(res);

        for (auto& map_pair : intersect_map) {
            cout << map_pair.first << " -> " << endl;
            for (auto& vec : map_pair.second) {
                for (auto s : vec) {
                    cout << s << " ";
                }
                cout << endl;
            }
        }
        cout << "=========" << endl;

        typedef unordered_map<State, unordered_map<State, vector<Registers> > > Trans;
        vector<Trans> trans_vec(idcras.size());

        typename DFA::StateIter sit, send;
        for (tie(sit, send) = atl::states(res); sit != send; sit ++) {
            auto s = *sit;
            typename DFA::OutTransitionIter it, end;
            for (tie(it, end) = out_transitions(res, s); it != end; it++) {
                auto t = atl::target(res, *it);
                const auto& c = atl::get_property(res, *it);
                auto& vecs_s = intersect_map[s];
                auto& vecs_t = intersect_map[t];
                vector<StateSet> sources_vec(idcras.size());
                vector<StateSet> targets_vec(idcras.size());
                for (auto& vec_s : vecs_s) {
                    for (auto& vec_t : vecs_t) {
                        for (ID i = 0; i < idcras.size(); i++) {
                            auto& h_map = h_maps[i];
                            auto& r_map = r_maps[i];
                            auto& trans = trans_vec[i];
                            auto& sources = sources_vec[i];
                            auto& targets = targets_vec[i];
                            auto& states_s = h_map[vec_s[i]];
                            auto& states_t = h_map[vec_t[i]];
                            for (auto state_s : states_s) {
                                for (auto state_t : states_t) {
                                    StatePair state_pair(state_s, state_t);
                                    auto& rs = r_map[state_pair][c];
                                    if (rs.size() > 0) {
                                        auto& rs_vec = trans[state_s][state_t];
                                        rs_vec.insert(rs_vec.end(), rs.begin(), rs.end());
                                        sources.insert(state_s);
                                        targets.insert(state_t);
                                    }
                                }
                            }
                        }
                    }
                }
                cout << "size" << endl;
                for (auto& sources : sources_vec)
                    cout << sources.size() << " ";
                cout << endl;
                for (auto& targets : targets_vec)
                    cout << targets.size() << " ";
                cout << endl;
            }
        }


        //unordered_map<vector<State>, State> vec_map;
        //for (auto& map_pair : intersect_map) {
        //    for (auto& vec : map_pair.second) {
        //        for (ID i = 0; i < vec.size(); i++) {
        //            for (auto s : h_maps[i][vec[i]]) {
        //                cout << s << " ";
        //            }
        //            cout << endl;
        //        }
        //    }
        //    cout << endl;
        //    cout << endl;
        //}

        //if (atl::get_property(res).names().size() == 0) continue;
        //NRA nra;
        //toNRA(res, nra);
        //DRA dra = minimize(determinize(nra));
        //string name = "_" + std::to_string(i++);
        ////encode_idcra(res, name, *fa_, f);
        //encode_dra(dra, name, *fa_, f);
    }
    //atl::set_property(*fa_, f);
    //nuxmvSolver_ = new nuxmv::nuxmv_solver(fa_);
    //nuxmvSolver_ -> solve(timeout);
    //return 1;
}

void StrSolver::solve2(const string& timeout, int window, const string& engine) {
    fa_ = new fomula_automaton();
    for (auto& var : undeclaredVar_) {
        //add_input_state(*fa_, int_variable(var));
        auto uvar = window > 0 ? int_variable(var, window * -1, window) : int_variable(var);
        add_input_state(*fa_, uvar);
    }

    ID i = 0;
    auto f = fomula_;
    for (auto& idcras : idcrasList_) {
        if (idcras.size() == 1 && atl::get_property(*idcras.front()).names().size() == 0)
            continue;
        string name = "_" + std::to_string(i++);
        auto cvar = int_variable("c" + name, 0, 128);
        auto cstate = add_input_state(*fa_, cvar);
        ID j = 0;
        for (auto idcra : idcras) {
            string name_ = name + "_" + std::to_string(j++);
            encode_idcra(*idcra, name_, *fa_, f, cvar, window);
        }
    }
    atl::set_property(*fa_, f);
    nuxmvSolver_ = new nuxmv::nuxmv_solver(fa_);
    nuxmvSolver_ -> solve(engine, timeout);
    //return 1;
}

void StrSolver::solve(const string& timeout) {
    getCounterIdcrasList();
    fa_ = new fomula_automaton();
    for (auto& var : undeclaredVar_) {
        add_input_state(*fa_, int_variable(var));
    }
    ID i = 0;
    auto f = fomula_;
    for (auto& idcras : counterIdcrasList_) {
        IDCRA res = minimize(*(idcras.front()));
        for (auto fa : idcras) {
            if (fa == idcras.front()) continue;
            res = get_intersect_fa(res, minimize(*fa));
        }
        if (is_empty(res)) {
            cout << "intersection is empty, this is true !" << endl;
            return;
        }
        if (atl::get_property(res).names().size() == 0) continue;
        NRA nra;
        toNRA(res, nra);
        DRA dra = minimize(nra);
        string name = "_" + std::to_string(i++);
        encode_dra(dra, name, *fa_, f);
    }
    atl::set_property(*fa_, f);
    nuxmvSolver_ = new nuxmv::nuxmv_solver(fa_);
    nuxmvSolver_ -> solve(timeout);
    //return 1;
}

void StrSolver::encode_dra(const DRA& dra, const string& name, fomula_automaton& fa, propositional_fomula& final_fomula) {
    vector<ll::enum_value> values;
    typename IDCRA::StateIter it, end;
    boost::unordered_map<ID, ID> stateMap;
    for (tie(it, end) = states(dra); it != end; it++) {
        auto value = enum_value("v" + std::to_string(*it));
        values.push_back(value);
        stateMap[*it] = add_state(fa, value);
    }
    auto tvalue = enum_value("t");
    auto tstate = add_state(fa, tvalue);
    values.push_back(tvalue);
    auto svar = enum_variable("s" + name, values.begin(), values.end());
    auto state = add_control_state(fa, svar,
                                   svar == atl::get_property(fa, 
                                                stateMap[dra.initial_state()]));

    propositional_fomula ff("FALSE");
    for (auto fs : dra.final_state_set()) {
        ff = (ff | (svar == atl::get_property(fa, stateMap[fs])));
    }

    final_fomula = final_fomula & ff;

    boost::unordered_map<string, ID> registerNamesMap;
    boost::unordered_map<ID, ID> registersMap;
    ID rid = 0;
    for (auto& rname : atl::get_property(dra).names()) {
        auto rvar = int_variable(rname);
        auto rs = add_control_state(fa, rvar, rvar == int_value(0));
        add_state(fa, int_variable(rname + " + 1"));
        registerNamesMap[rname] = rs;
        registersMap[rid++] = rs;
    }

    boost::unordered_map<Registers, ll::enum_value> registers2ValueMap;
    values.clear();
    auto cvar = enum_variable("c" + name);
    for (auto& r : alphabet(dra)) {
        auto value = enum_value(r.to_string());
        values.push_back(value);
        registers2ValueMap[r] = value;
    }

    auto cstate = add_input_state(fa, enum_variable("c" + name, values.begin(), values.end()));

    for (tie(it, end) = states(dra); it != end; it++) {
        typename DRA::OutTransitionIter tit, tend;
        for (tie(tit, tend) = out_transitions(dra, *it); tit != tend; tit++) {
            const auto& t = atl::get_property(dra, *tit);
            auto f = (atl::get_property(fa, state) == atl::get_property(fa, stateMap[*it]) &
                      atl::get_property(fa, cstate) == registers2ValueMap[t]);
            const auto& nums = t.nums();
            add_transition(fa, state, stateMap[atl::target(dra, *tit)], f);

            for (int i = 0; i < nums.size(); i++) {
                auto rstate = registersMap[i];
                if (nums[i] == 1) {
                    add_transition(fa, rstate, rstate + 1, f);
                } else {
                    add_transition(fa, rstate, rstate, f);
                }
            }
        }
    }
    auto trueFomula = propositional_fomula("TRUE");
    add_transition(fa, state, tstate, trueFomula);
    for (auto& rname : atl::get_property(dra).names()) {
        auto rstate = registerNamesMap[rname];
        add_transition(fa, rstate, rstate, trueFomula);
    }
}

void StrSolver::encode_idcra(const IDCRA& idcra, const string& name, fomula_automaton& fa, propositional_fomula& final_fomula, const int_variable& cvar, int window) {
    vector<ll::enum_value> values;
    typename IDCRA::StateIter it, end;
    boost::unordered_map<ID, ID> stateMap;
    for (tie(it, end) = states(idcra); it != end; it++) {
        auto value = enum_value("v" + std::to_string(*it));
        values.push_back(value);
        stateMap[*it] = add_state(fa, value);
    }
    auto tvalue = enum_value("t");
    auto tstate = add_state(fa, tvalue);
    values.push_back(tvalue);
    auto svar = enum_variable("s" + name, values.begin(), values.end());
    auto state = add_control_state(fa, svar,
                                   svar == atl::get_property(fa, 
                                                stateMap[idcra.initial_state()]));

    auto trueFomula = propositional_fomula("TRUE");


    boost::unordered_map<string, ID> registerNamesMap;
    boost::unordered_map<ID, ID> registersMap;
    ID rid = 0;
    propositional_fomula register_true_fomula("TRUE");
    for (auto& rname : atl::get_property(idcra).names()) {
        auto rvar = window > 0 ? int_variable(rname, window * -1, window) : int_variable(rname);
        //auto rvar = int_variable(rname, 0, window);
        auto s = add_control_state(fa, rvar, rvar == int_value(0));
        registerNamesMap[rname] = s;
        add_state(fa, int_variable(rname + " + 1"));
        auto bvar = bool_variable("r_" + rname);
        if (window == 0) {
            add_transition(fa, s, s + 1, (bvar == bool_value(1)));
        } else {
            add_transition(fa, s, s + 1, (bvar == bool_value(1)) & (rvar < int_value(window)));
        }
        //add_transition(fa, s, s + 1, (bvar == bool_value(1)));
        add_transition(fa, s, s, trueFomula);
        registersMap[rid++] = add_input_state(fa, bvar);
        register_true_fomula = (register_true_fomula & (bvar == bool_value(0)));
    }

    propositional_fomula ff("FALSE");
    for (auto fs : idcra.final_state_set()) {
        auto fs_ = stateMap[fs];
        auto& value = atl::get_property(fa, fs_);
        //add_transition(fa, state, fs_, (((svar == value) & cvar == int_value(128)) & register_true_fomula));
        ff = (ff | (svar == value));
    }
    add_transition(fa, state, stateMap[*(idcra.final_state_set().begin())], ((ff & cvar == int_value(128)) & register_true_fomula));
    final_fomula = final_fomula & ff;

    for (tie(it, end) = states(idcra); it != end; it++) {
        typename IDCRA::OutTransitionIter tit, tend;
        for (tie(tit, tend) = out_transitions(idcra, *it); tit != tend; tit++) {
            const auto& t = atl::get_property(idcra, *tit);
            auto f = (atl::get_property(fa, state) == atl::get_property(fa, stateMap[*it]) &
                      (cvar >= int_value(t.symbol.min())) &
                       cvar <= int_value(t.symbol.max()));
            const auto& nums = t.symbol_property.nums();
            for (int i = 0; i < nums.size(); i++) {
                if (nums[i] == 1) {
                    f = f & (atl::get_property(fa, registersMap[i]) == bool_value(1));
                } else {
                    f = f & (atl::get_property(fa, registersMap[i]) == bool_value(0));
                }
            }
            add_transition(fa, state, stateMap[atl::target(idcra, *tit)], f);
            //for (int i = 0; i < nums.size(); i++) {
            //    auto rstate = registersMap[i] - 2;
            //    if (nums[i] == 1) {
            //        add_transition(fa, rstate, rstate + 1, f & 
            //                (atl::get_property(fa, registersMap[i] - 2) < int_value(window)));
            //    } else {
            //        add_transition(fa, rstate, rstate, f);
            //    }
            //}
        }
    }
    add_transition(fa, state, tstate, trueFomula);
    //for (auto& rname : atl::get_property(idcra).names()) {
    //    auto rstate = registerNamesMap[rname];
    //    add_transition(fa, rstate, rstate, trueFomula);
    //}
}

void StrSolver::encode_idcra(const IDCRA& idcra, const string& name, fomula_automaton& fa, propositional_fomula& final_fomula) {
    vector<ll::enum_value> values;
    typename IDCRA::StateIter it, end;
    boost::unordered_map<ID, ID> stateMap;
    for (tie(it, end) = states(idcra); it != end; it++) {
        auto value = enum_value("v" + std::to_string(*it));
        values.push_back(value);
        stateMap[*it] = add_state(fa, value);
    }
    auto tvalue = enum_value("t");
    auto tstate = add_state(fa, tvalue);
    values.push_back(tvalue);
    auto svar = enum_variable("s" + name, values.begin(), values.end());
    auto state = add_control_state(fa, svar,
                                   svar == atl::get_property(fa, 
                                                stateMap[idcra.initial_state()]));

    propositional_fomula ff("FALSE");
    for (auto fs : idcra.final_state_set()) {
        ff = (ff | (svar == atl::get_property(fa, stateMap[fs])));
    }

    final_fomula = final_fomula & ff;

    boost::unordered_map<string, ID> registerNamesMap;
    boost::unordered_map<ID, ID> registersMap;
    ID rid = 0;
    for (auto& rname : atl::get_property(idcra).names()) {
        auto rvar = int_variable(rname);
        registerNamesMap[rname] = add_control_state(fa, rvar, rvar == int_value(0));
        add_state(fa, int_variable(rname + " + 1"));
        registersMap[rid++] = add_input_state(fa, bool_variable("r_" + rname));
    }

    boost::unordered_map<Label, ll::enum_value> label2ValueMap;
    values.clear();
    auto cvar = enum_variable("c" + name);
    for (auto& l : alphabet(idcra)) {
        auto value = enum_value(l.to_string());
        values.push_back(value);
        label2ValueMap[l] = value;
        auto lvar = int_variable("r_" + l.to_string() + name);
        auto lstate = add_control_state(fa, lvar,
                                        lvar == int_value(0));
        add_transition(fa, lstate,
                       add_state(fa, int_variable("r_" + l.to_string() + name + " + 1")),
                       (cvar == value));
        add_transition(fa, lstate, lstate, propositional_fomula("TRUE"));
    }

    auto cstate = add_input_state(fa, enum_variable("c" + name, values.begin(), values.end()));

    for (tie(it, end) = states(idcra); it != end; it++) {
        typename IDCRA::OutTransitionIter tit, tend;
        for (tie(tit, tend) = out_transitions(idcra, *it); tit != tend; tit++) {
            const auto& t = atl::get_property(idcra, *tit);
            auto f = (atl::get_property(fa, state) == atl::get_property(fa, stateMap[*it]) &
                      atl::get_property(fa, cstate) == label2ValueMap[t.symbol]);
            const auto& nums = t.symbol_property.nums();
            for (int i = 0; i < nums.size(); i++) {
                if (nums[i] == 1) {
                    f = f & (atl::get_property(fa, registersMap[i]) == bool_value(1));
                } else {
                    f = f & (atl::get_property(fa, registersMap[i]) == bool_value(0));
                }
            }
            add_transition(fa, state, stateMap[atl::target(idcra, *tit)], f);
            for (int i = 0; i < nums.size(); i++) {
                auto rstate = registersMap[i] - 2;
                if (nums[i] == 1) {
                    add_transition(fa, rstate, rstate + 1, f);
                } else {
                    add_transition(fa, rstate, rstate, f);
                }
            }
        }
    }
    auto trueFomula = propositional_fomula("TRUE");
    add_transition(fa, state, tstate, trueFomula);
    for (auto& rname : atl::get_property(idcra).names()) {
        auto rstate = registerNamesMap[rname];
        add_transition(fa, rstate, rstate, trueFomula);
    }
}

void StrSolver::encode() {
    fa_ = new fomula_automaton();
    for (auto& var : undeclaredVar_) {
        add_input_state(*fa_, int_variable(var));
    }
    ID i = 0;
    auto f = fomula_;
    for (auto& idcras : counterIdcrasList_) {
        ID j = 0;
        for (auto idcra : idcras) {
            string name = "_" + std::to_string(i) + "_" + std::to_string(j);
            encode_idcra(*idcra, name, *fa_, f);
            if (j > 0) {
                string name1 = "_" + std::to_string(i) + "_" + std::to_string(j - 1);
                for (auto& l : alphabet(*idcra)) {
                    string lname = "r_" + l.to_string();
                    f = (f & (propositional_fomula((lname + name1) + "=" + (lname + name))));
                }
            }
            j++;
        }
        i++;
    }
    atl::set_property(*fa_, f);
    nuxmvSolver_ = new nuxmv::nuxmv_solver(fa_);
    //nuxmvSolver_ -> solve();
}

