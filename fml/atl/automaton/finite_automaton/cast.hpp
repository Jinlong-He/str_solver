//
//  cast.hpp
//  ATL 
//
//  Created by Jinlong He on 2019/11/12.
//  Copyright © 2019年 Ruting-Team. All rights reserved.
//

#ifndef atl_finite_automaton_cast_hpp 
#define atl_finite_automaton_cast_hpp 

#include <queue>
#include "../detail/automaton.hpp"
#include "../automaton_utility.hpp"
#include "deterministic_finite_automaton.hpp"
#include "nondeterministic_finite_automaton.hpp"
#include "closure.hpp"
#include "merge.hpp"
using std::queue;
using std::cout;
using std::endl;

namespace atl {
    struct minimize_impl {
        template <typename DFA>
        static bool 
        is_equal(const DFA& dfa,
                 typename DFA::State s1,
                 typename DFA::State s2,
                 typename DFA::State2Map const& state2_map) {
            const auto& transition_map = dfa.transition_map();
            if constexpr (!std::is_same<typename DFA::state_property_type, 
                                        boost::no_property>::value) {
                if (atl::get_property(dfa, s1) != atl::get_property(dfa, s2)) return false;
            }
            ID count1 = transition_map.count(s1), count2 = transition_map.count(s2);
            if (count1 == 0 && count2 == 0) return true;
            if ((count1 & count2) == 0) return false;
            auto &map1 = transition_map.at(s1);
            auto &map2 = transition_map.at(s2);
            if (map1.size() != map2.size()) return false;
            for (auto& map_pair : map1) {
                if (map2.count(map_pair.first) == 0) return false;

                if constexpr (std::is_same<typename DFA::symbol_property_type, 
                                            no_type>::value) {
                    if (state2_map.count(map_pair.second) & 
                        state2_map.count(map2.at(map_pair.first))) continue;
                    if (state2_map.at(map_pair.second) != 
                        state2_map.at(map2.at(map_pair.first))) return false;
                } else {
                    auto& map1_ = map_pair.second;
                    auto& map2_ = map2.at(map_pair.first);
                    if (map1_.size() != map2_.size()) return false;
                    for (auto& map_pair1 : map1_) {
                        if (map2_.count(map_pair1.first) == 0) return false;
                        //if (state2_map.count(map_pair1.second) & 
                        //    state2_map.count(map2_.at(map_pair1.first))) continue;
                        if (state2_map.at(map_pair1.second) != 
                            state2_map.at(map2_.at(map_pair1.first))) return false;
                    }
                }
            }
            return true;
        }

        template <typename DFA>
        static void 
        get_equivalences(const DFA& a_in, 
                         DFA& a_out,
                         queue<typename DFA::StateSet>& eqs, 
                         typename DFA::State2Map& state2_map) {
            typedef typename DFA::State State;
            typedef typename DFA::StateSet StateSet;
            typedef typename DFA::State2Map State2_map;
            ID cur_size = eqs.size(), last_size = 0;
            while (cur_size != last_size) {
                for (ID i = 0; i < cur_size; ++i) {
                    StateSet& set = eqs.front();
                    if (set.size() == 0) continue;
                    while (set.size() > 0) {
                        State state = *(set.begin());
                        StateSet new_eqs;
                        new_eqs.insert(state);
                        set.erase(state);
                        StateSet delStateSet;
                        for (const auto& new_state : set) {
                            if (is_equal(a_in, state, new_state, state2_map)) {
                                new_eqs.insert(new_state);
                                delStateSet.insert(new_state);
                            }
                        }
                        eqs.push(new_eqs);
                        for (auto delState : delStateSet) {
                            set.erase(delState);
                        }
                        State new_map_state = -1;
                        if constexpr (std::is_same<typename DFA::state_property_type, 
                                                   boost::no_property>::value) {
                            new_map_state = add_state(a_out);
                        } else {
                            new_map_state = add_state(a_out, atl::get_property(a_in, 
                                                                  *(new_eqs.begin())));
                        }
                        for (auto new_state : new_eqs) {
                            state2_map[new_state] = new_map_state;
                        }
                    }
                    eqs.pop();
                }
                last_size = cur_size;
                cur_size = eqs.size();
            }
        }

        template <typename DFA>
        static void 
        apply(const DFA& a_in,
              DFA& a_out) {
            typedef typename DFA::State State;
            typedef typename DFA::StateSet StateSet;
            typedef typename DFA::State2Map State2Map;
            typedef typename DFA::TransitionMap TransitionMap;
            typedef typename DFA::state_property_type StateProperty;
            StateSet reachable_states, unfinal_states, final_states;
            atl::clear(a_out);
            atl::reachable_closure(a_in, reachable_states);
            State2Map state2_map;
            State unfinal_state = add_state(a_out),
                  final_state = add_state(a_out);
            typename DFA::State2Map copy_map;;
            DFA dfa;
            for (auto state : reachable_states) {
                auto s = add_state(dfa);
                copy_map[state] = s;
                if (state == a_in.initial_state()) dfa.set_initial_state(s);
                if (is_final_state(a_in, state)) set_final_state(dfa, s);
            }

            for (auto state : reachable_states) {
                typename DFA::OutTransitionIter it, end;
                for (tie(it, end) = out_transitions(a_in, state); it != end; it++) {
                    auto target_state = atl::target(a_in, *it);
                    if (reachable_states.count(target_state) == 0) continue;
                    add_transition(dfa, copy_map[state], copy_map[target_state],
                                   atl::get_property(a_in, *it));
                }
            }

            //cout << "*****************" << endl;
            //print_fa(a_in);
            //print_fa(dfa);
            //cout << "*****************" << endl;

            typename DFA::StateIter it, end;
            for (tie(it, end) = states(dfa); it != end; it++) {
                auto state = *it;
                if (is_final_state(dfa, state)) {
                    final_states.insert(state);
                    state2_map[state] = final_state;
                } else {
                    unfinal_states.insert(state);
                    state2_map[state] = unfinal_state;
                }
            }

            //for (auto state : reachable_states) {
            //    if (is_final_state(a_in, state)) {
            //        final_states.insert(state);
            //        state2_map[state] = final_state;
            //    } else {
            //        unfinal_states.insert(state);
            //        state2_map[state] = unfinal_state;
            //    }
            //}

            std::queue<StateSet> eqs({final_states});
            if (unfinal_states.size() > 0) eqs.push(unfinal_states);
            get_equivalences(dfa, a_out, eqs, state2_map);

            atl::clear(a_out);
            atl::set_alphabet(a_out, atl::get_alphabet(dfa));
            if constexpr (!std::is_same<typename DFA::automaton_property_type, 
                                        boost::no_property>::value) {
                //atl::set_property(a_out, atl::get_property(dfa));
                atl::set_property(a_out, atl::get_property(a_in));
            }
            
            State initial_state = -1;
            if constexpr (std::is_same<typename DFA::state_property_type, 
                                       boost::no_property>::value) {
                initial_state = add_initial_state(a_out);
            } else {
                initial_state = add_initial_state(a_out, atl::get_property(dfa, 
                                                              dfa.initial_state()));
            }

            if (is_final_state(dfa, dfa.initial_state())) 
                a_out.set_final_state(initial_state);

            State2Map new_state2_map({{dfa.initial_state(), initial_state}}),
                      map({{state2_map[dfa.initial_state()], initial_state}});
            for (auto& map_pair : state2_map) {
                State state = map_pair.second;
                if (map.count(state) == 0) {
                    State new_state = -1;
                    if constexpr (std::is_same<typename DFA::state_property_type, 
                                               boost::no_property>::value) {
                        new_state = add_state(a_out);
                    } else {
                        new_state = add_state(a_out, atl::get_property(dfa, map_pair.first));
                    }

                    if (is_final_state(dfa, map_pair.first)) 
                        a_out.set_final_state(new_state);
                    new_state2_map[map_pair.first] = new_state;
                    map[state] = new_state;
                } else {
                    new_state2_map[map_pair.first] = map[state];
                }
            }

            const auto& transition_map = dfa.transition_map();
            for (auto& map_pair : new_state2_map) {
                if (map_pair.first == -1 || map_pair.second == -1) continue;
                ID count1 = transition_map.count(map_pair.first), 
                   count2 = a_out.transition_map().count(map_pair.second);
                if (count1 > 0 && count2 == 0) {
                    const auto &map = transition_map.at(map_pair.first);
                    for (auto& map_pair1 : map) {
                        if constexpr (!std::is_same<typename DFA::symbol_property_type, 
                                                    no_type>::value) {
                            for (auto& map_pair2 : map_pair1.second) {
                                if (reachable_states.count(map_pair2.second) == 0) continue;
                                add_transition(a_out,
                                               map_pair.second, 
                                               new_state2_map.at(map_pair2.second),
                                               map_pair1.first, map_pair2.first);
                            }
                        } else {
                            if (reachable_states.count(map_pair1.second) == 0) continue;
                            add_transition(a_out,
                                           map_pair.second, new_state2_map.at(map_pair1.second),
                                           map_pair1.first);
                        }
                    }
                }
            }
        }
    };

    template <typename DFA>
    inline void
    minimize(const DFA& a_in,
             DFA& a_out) {
        minimize_impl::apply(a_in, a_out);
    }

    template <typename DFA>
    inline DFA 
    minimize(const DFA& a_in) {
        DFA a_out;
        minimize_impl::apply(a_in, a_out);
        return a_out;
    }

    template <typename FA>
    inline void
    minimize(const FA& a_in,
             typename FA::DFA& a_out) {
        minimize_impl::apply(a_in, a_out);
    }
    
    //template <typename FiniteAutomaton,
    //          typename DeterministicFiniteAutomaton>
    //inline void
    //minimize(const FiniteAutomaton& a_in, 
    //         DeterministicFiniteAutomaton& a_out) {
    //    if (is_minimal(a_in)) {
    //        copy_fa(a_in, a_out);
    //    } else {
    //        if (typeid(a_in) != typeid(DeterministicFiniteAutomaton)) {
    //            DeterministicFiniteAutomaton dfa;
    //            determinize(dynamic_cast< 
    //                        typename FiniteAutomaton::NondeterministicFiniteAutomatonType const&>
    //                        (a_in), dfa);
    //            MinimizeImpl::apply(dfa, a_out);
    //        } else {
    //            MinimizeImpl::apply(dynamic_cast<const DeterministicFiniteAutomaton&>(a_in),
    //                                a_out);
    //        }
    //        set_minimal_flag(a_out);
    //    }
    //}

    //template <typename FiniteAutomaton,
    //          typename DeterministicFiniteAutomaton>
    //inline void
    //minimize(const FiniteAutomaton& a_in, 
    //         std::shared_ptr<const DeterministicFiniteAutomaton>& a_out) {
    //    if (!is_minimal(a_in)) {
    //        std::shared_ptr<DeterministicFiniteAutomaton> dfa_ptr = nullptr;
    //        dfa_ptr = std::make_shared<DeterministicFiniteAutomaton>();
    //        minimize(a_in, *dfa_ptr);
    //        a_out = dfa_ptr;
    //    } else {
    //        std::shared_ptr<const DeterministicFiniteAutomaton> 
    //        ptr(dynamic_cast<const DeterministicFiniteAutomaton*>(&a_in));
    //        a_out = ptr;
    //    }
    //}

    struct remove_epsolon_impl {
        template <typename NFA, 
                  typename StateMerge,
                  typename SymbolPropertyMerge>
        static void
        apply(const NFA& a_in, 
              NFA& a_out, 
              StateMerge state_merge,
              SymbolPropertyMerge symbol_property_merge) {
            typedef typename NFA::State State;
            typedef typename NFA::state_property_type StateProp;
            if constexpr (std::is_same<typename NFA::symbol_property_type, no_type>::value) {
                typename NFA::StateSet set;
                typename NFA::StateSetMap set_map;
                typename NFA::State2Map state2_map;
                typename NFA::StateIter it, end;
                for (tie(it, end) = states(a_in); it != end; it++) {
                    set.clear();
                    set.insert(*it);
                    epsilon_closure(*it, set, a_in);
                    State state = -1;
                    auto iter = set_map.find(set);
                    if (iter == set_map.end()) {
                        if constexpr (std::is_same<StateProp, boost::no_property>::value) {
                            state = add_state(a_out);
                        } else {
                            std::vector<StateProp> props;
                            for (auto s : set)
                                props.push_back(atl::get_property(a_in, s));
                            state = add_state(a_out, state_merge(props));
                        }
                        if (*it == a_in.initial_state()) a_out.set_initial_state(state);
                        if (has_final_state(a_in, set)) a_out.set_final_state(state);
                        set_map[set] = state;
                    } else {
                        state = iter -> second;
                    }
                    state2_map[*it] = state;
                }

                typename NFA::TransitionIter t_it, t_end;
                for (tie(t_it, t_end) = transitions(a_in); t_it != t_end; t_it++) {
                    State source = state2_map[atl::source(a_in, *t_it)];
                    State target = state2_map[atl::target(a_in, *t_it)];
                    add_transition(a_out, source, target, atl::get_property(a_in, *t_it));
                }
            } else {
                //todo
            }
        }
    };

    struct determinize_impl {
        template <typename NFA>
        static void 
        get_determinize_map(const NFA& nfa,
                            typename NFA::StateSet const& states, 
                            typename NFA::Symbol2StateSetMap& map) {
            typename NFA::StateSet new_states;
            for (const auto& state : states) {
                if (nfa.transition_map().count(state) == 0) continue;
                for (auto& map_pair : nfa.transition_map().at(state)) {
                    const auto& symbol = map_pair.first;
                    if constexpr (std::is_same<typename NFA::symbol_property_type, 
                                               no_type>::value) {
                        if (symbol == nfa.epsilon()) continue;
                        new_states.clear();
                        get_targets_in_map(nfa, state, symbol, new_states);
                        if (new_states.size() > 0) {
                            epsilon_closure(nfa, new_states, new_states);
                            map[symbol].insert(new_states.begin(), new_states.end());
                        }
                    } else {
                        for (auto& map_pair1 : map_pair.second) {
                            const auto& symbol_property = map_pair1.first;
                            new_states.clear();
                            get_targets_in_map(nfa, state, symbol, symbol_property, new_states);
                            if (new_states.size() > 0) {
                                map[symbol][symbol_property].insert(new_states.begin(), 
                                                                    new_states.end());
                            }
                        }
                    }
                }
            }
        }

        template <typename NFA, 
                  typename DFA,
                  typename StateMerge>
        static void 
        add_determinize_transition(const NFA& nfa,
                                   DFA& dfa,
                                   typename NFA::State source,
                                   typename NFA::StateSet const& state_set,
                                   typename NFA::StateSetMap& set_map,
                                   typename DFA::transition_property_type const& t,
                                   StateMerge state_merge) {
            typedef typename NFA::State State;
            State target = -1;
            auto set_iter = set_map.find(state_set);
            if (set_iter == set_map.end()) {
                if constexpr (std::is_same<typename NFA::state_property_type, 
                                           boost::no_property>::value) {
                    target = add_state(dfa);
                } else {
                    std::vector<typename NFA::state_property_type> props;
                    for (const auto& s : state_set)
                        props.push_back(atl::get_property(nfa, s));
                    target = add_state(dfa, merge(props.begin(), props.end()));
                }
                set_map[state_set] = target;
                do_determinize(nfa, dfa, target, state_set, set_map, state_merge);
            } else {
                target = set_iter -> second;
            }
            add_transition(dfa, source, target, t);
        }

        template <typename NFA, 
                  typename DFA,
                  typename Merge>
        static void 
        do_determinize(const NFA& nfa,
                       DFA& dfa,
                       typename DFA::State source,
                       typename NFA::StateSet const& state_set,
                       typename NFA::StateSetMap& set_map,
                       Merge merge) {
            if (has_final_state(nfa, state_set)) set_final_state(dfa, source);
            typename NFA::Symbol2StateSetMap map;
            typedef typename NFA::transition_property_type TransitionProperty;
            typedef typename NFA::state_property_type StateProp;
            typedef typename NFA::State State;
            get_determinize_map(nfa, state_set, map);
            for (auto& map_pair : map) {
                const auto& symbol = map_pair.first;
                if constexpr (std::is_same<typename NFA::symbol_property_type, 
                                           no_type>::value) {
                    add_determinize_transition(nfa, dfa, source, map_pair.second, set_map, 
                                               symbol, merge);
                } else {
                    for (auto& map_pair1 : map_pair.second) {
                        const auto& symbol_property = map_pair1.first;
                        add_determinize_transition(nfa, dfa, source, map_pair1.second, set_map, 
                                                   TransitionProperty(symbol, symbol_property), 
                                                   merge);
                    }
                }
            }
        }

        template <typename NFA, 
                  typename StateMerge,
                  typename SymbolPropertyMerge>
        static void apply(const NFA& nfa,
                          typename NFA::DFA& dfa,
                          StateMerge state_merge,
                          SymbolPropertyMerge symbol_property_merge) {
            atl::clear(dfa);
            atl::set_alphabet(dfa, atl::get_alphabet(nfa));
            if constexpr (!std::is_same<typename NFA::automaton_property_type, 
                                        boost::no_property>::value) {
                atl::set_property(dfa, atl::get_property(nfa));
            }
            if constexpr (std::is_same<typename NFA::symbol_property_type, 
                                       no_type>::value) {
                typename NFA::StateSet states;
                epsilon_closure(nfa, states);
                typename NFA::State initial_state = -1;
                if constexpr (std::is_same<typename NFA::state_property_type, 
                                           boost::no_property>::value) {
                    initial_state = add_initial_state(dfa);
                } else {
                    std::vector<typename NFA::state_property_type> props;
                    for (const auto& s : states) 
                        props.push_back(atl::get_property(nfa, s));
                    initial_state = add_initial_state(dfa, state_merge(props.begin(), 
                                                                       props.end()));
                }
                typename NFA::StateSetMap states_map({{states, initial_state}});
                do_determinize(nfa, dfa, dfa.initial_state(), states, states_map,
                               symbol_property_merge);
            } else {
                typename NFA::State initial_state = -1;
                if constexpr (std::is_same<typename NFA::state_property_type, 
                                           boost::no_property>::value) {
                    initial_state = add_initial_state(dfa);
                } else {
                    initial_state = add_initial_state(dfa, 
                                        atl::get_property(nfa, nfa.initial_state()));
                }
                typename NFA::StateSetMap states_map({{states, initial_state}});
                do_determinize(nfa, dfa, dfa.initial_state(), states, states_map,
                               symbol_property_merge);
            }
        }
    };

    template <typename NFA,
              typename Merge = union_merge<typename NFA::state_property_type> >
    inline void
    determinize(const NFA& a_in, 
                typename NFA::DFA& a_out,
                Merge merge = Merge()) {
        if (!is_undeterministic(a_in)) {
            clear(a_out);
            //a_out = a_in;
        } else {
            determinize_impl::apply(a_in, a_out, merge);
            set_forwar_reachable_flag(a_out);
        }
    }

    template <typename NFA>
    inline typename NFA::DFA 
    determinize(const NFA& a_in) {
        typename NFA::DFA a_out;
        determinize_impl::apply(a_in, a_out, 
                         intersect_merge<typename NFA::state_property_type>(),
                         intersect_merge<typename NFA::symbol_property_type>());
        return a_out;
    }
}

#endif /* atl_finite_automaton_cast_hpp */
