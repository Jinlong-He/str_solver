//
//  str_solver.hpp
//
//  Created by Jinlong He on 2019/12/10.
//  Copyright © 2019年 Jinlong He. All rights reserved.
//

#ifndef str_solver_hpp 
#define str_solver_hpp
#include <unordered_set>
#include <set>
#include "idcra.hpp"
#include "idcra_parser.hpp"
#include "../nuxmv/nuxmv_solver.hpp"
#include "../../fml/atl/automaton/automaton_utility.hpp"

class StrSolver {
    typedef std::vector<string> strings;
public:
    StrSolver()
        : nuxmvSolver_(nullptr) {}

    StrSolver(const string& fileName)
        : nuxmvSolver_(nullptr) {
            strings strs;
            readFile(fileName, strs);
            parse(strs);
            getCounterIdcrasList();
            //encode();
        }

    ~StrSolver() {
        for (auto& idcras : idcrasList_) {
            for (auto idcra : idcras) {
                delete idcra;
            }
        }
        for (auto& idcras : counterIdcrasList_) {
            for (auto idcra : idcras) {
                delete idcra;
            }
        }
        delete fa_;
    }

    void solve(const string& timeout);
private:
    void readFile(const string& fileName, strings& strs);
    void parseIdcras(const strings& strs, IDCRAs& idcras);
    void parseIdcrasList(const strings& strs);
    void parseConstrain(const string& str);
    void parseDeclaration(const string& str);
    void parse(const strings& strs);

    void getCounterIdcrasList();

    void encode();
    void encode_idcra(const IDCRA& idcra, const string& name, fomula_automaton& fa, propositional_fomula& f);
    void encode_dra(const DRA& dra, const string& name, fomula_automaton& fa, propositional_fomula& f);
private:
    IDCRAsList idcrasList_;
    IDCRAsList counterIdcrasList_;
    //IDCRAs idcras_;
    ll::propositional_fomula fomula_;
    fomula_automaton* fa_;
    nuxmv::nuxmv_solver* nuxmvSolver_;
    strings undeclaredVar_;
};

#endif /* str_solver_hpp */
