//
//  nuxmv_solver.hpp
//   
//
//  Created by Jinlong He on 2019/12/7.
//  Copyright © 2019年 Ruting-Team. All rights reserved.
//

#ifndef nuxmv_solver_hpp 
#define nuxmv_solver_hpp
#include <fstream>
#include "nuxmv_parser.hpp"
#include "nuxmv_translator.hpp"
namespace nuxmv {
    class nuxmv_solver {
    public:
        nuxmv_solver()
            : translator_(nullptr),
              parser_(nullptr),
              fa_(nullptr) {}

        nuxmv_solver(fomula_automaton* fa)
            : translator_(new nuxmv_translator(fa)),
              parser_(new nuxmv_parser(fa)),
              fa_(fa) {}

        void solve(const string& engine, const string& timeout = "0") {
            std::fstream fs;
            fs.open ("out.smv", std::fstream::out);
            if (fs.is_open()) {
                fs << translator_ -> translate_nuxmv_format();
            }
            fs.close();
            //string commond = "timeout " + std::to_string(timeout) + " nuXmv -source cmd_file out.smv";
            if (timeout == "" || timeout == "0") {
                //string commond = is_infinite(*fa_) ? "nuxmv -source cmd_file out.smv" : 
                //                                     "nuxmv out.smv";
                string commond = "nuxmv -dcx -source " + engine + " out.smv";
                std::cout << commond << std::endl;
                std::cout << system(commond.c_str()) << std::endl;
            } else {
                string time_str = "timeout " + timeout;
                string commond = time_str + " nuxmv -dcx -source " + engine + " out.smv";
                std::cout << commond << std::endl;
                std::cout << system(commond.c_str()) << std::endl;
            }
            //string result;
            //FILE* ptr = nullptr;
            //char buf_ps[2048];
            //if ((ptr = popen(commond.c_str(), "r")) != nullptr) {
            //    while(fgets(buf_ps, 2048, ptr) != nullptr)
            //        result.append(buf_ps);
            //    pclose(ptr);
            //    ptr = nullptr;
            //}
            //std::cout << result << std::endl;
            //std::cout << parser_ -> parse_result(result) << std::endl;
            //cout << commond << endl;
            //system("rm out.smv");
        }

        string smv_format() {
            return translator_ -> translate_nuxmv_format();
        }

    private:
        nuxmv_translator* translator_;
        nuxmv_parser* parser_;
        fomula_automaton* fa_;
    };
}

#endif /* nuxmv_solver_hpp */
