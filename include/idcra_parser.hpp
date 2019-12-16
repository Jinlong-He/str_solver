//
//  idcra_parser.hpp
//
//  Created by Jinlong He on 2019/12/10.
//  Copyright © 2019年 Jinlong He. All rights reserved.
//

#ifndef idcra_parser_hpp 
#define idcra_parser_hpp
#include "idcra.hpp"
#include "../nuxmv/nuxmv_solver.hpp"

class IdcraParser {
public:
    static void parse(const vector<string>& str, IDCRA& idcra);
};

#endif /* idcra_parser_hpp */
