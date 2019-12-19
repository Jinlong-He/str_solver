//
//  incra.hpp
//
//  Created by Jinlong He on 2019/12/08.
//  Copyright © 2019年 Jinlong He. All rights reserved.
//

#ifndef incra_hpp 
#define incra_hpp
#include "../fml/atl/automaton/finite_automaton/nondeterministic_finite_automaton.hpp"
#include "../fml/atl/automaton/finite_automaton/deterministic_finite_automaton.hpp"
#include "../fml/atl/automaton/finite_automaton/cast.hpp"
#include "../fml/atl/automaton/finite_automaton/operate.hpp"
#include "label.hpp"
#include "register.hpp"

typedef atl::nondeterministic_finite_automaton<Registers, -1, atl::no_type, 
                                               atl::no_type, RegisterNames> NRA;
typedef atl::deterministic_finite_automaton<Registers, -1, atl::no_type, 
                                            atl::no_type, RegisterNames> DRA;

typedef atl::nondeterministic_finite_automaton<Label, -1, atl::no_type, 
                                               atl::no_type, atl::no_type> NFA;
typedef atl::deterministic_finite_automaton<Label, -1, atl::no_type, 
                                            atl::no_type, atl::no_type> DFA;

typedef atl::deterministic_finite_automaton<Label, -1, Registers, 
                                               atl::no_type, RegisterNames> IDCRA;
typedef vector<IDCRA*> IDCRAs;
typedef std::list<IDCRAs> IDCRAsList;
typedef std::list<IDCRAsList> IDCRAsLists;

#endif /* incra_hpp */
