//
//  nuxmv_parser.hpp
//   
//
//  Created by Jinlong He on 2019/12/7.
//  Copyright © 2019年 Ruting-Team. All rights reserved.
//

#ifndef nuxmv_parser_hpp 
#define nuxmv_parser_hpp
#include <iostream>
#include <vector>
#include "../fml/atl/automaton/fomula_automaton/fomula_automaton.hpp"
using std::string;
using std::vector;
using namespace atl;
using namespace ll;
namespace nuxmv {
    class nuxmv_parser {
        typedef std::unordered_map<fomula_automaton, string> ValueMap;
        typedef std::list<ValueMap> ValueMaps;
    public:
        nuxmv_parser() 
            : fa_(nullptr) {}

        nuxmv_parser(fomula_automaton* fa)
            : fa_(fa) {}

        static bool
        parse_result(const string& result) {
            if (result.find("is true") != string::npos) return true;
            if (result.find("is false") != string::npos) return false;
            return true;
        }

        static void
        parse_counterexample(const vector<string>& trace);
    private:
        fomula_automaton* fa_;
    };
}

#endif /* nuxmv_parser_hpp */
