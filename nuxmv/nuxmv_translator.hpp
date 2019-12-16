//
//  nuxmv_translator.hpp
//   
//
//  Created by Jinlong He on 2019/12/7.
//  Copyright © 2019年 Ruting-Team. All rights reserved.
//

#ifndef nuxmv_translator_hpp 
#define nuxmv_translator_hpp
#include "../fml/atl/automaton/fomula_automaton/fomula_automaton.hpp"
using namespace atl;
using namespace ll;
namespace nuxmv {
    class nuxmv_translator {
    public:
        nuxmv_translator()
            : fa_(nullptr) {}

        nuxmv_translator(fomula_automaton* fa)
            : fa_(fa) {}

        //string& translate_declaration();
        //string& translate_initialization();
        //string& translate_transition();
        //string& translate_specification(const string& type);
        //string translate_nuxmv_format(const string& type = "INVARSPEC");
        string& translate_declaration() {
            for (auto s : control_state_set(*fa_)) {
                const auto& p = atl::get_property(*fa_, s);
                declaration_ += ("VAR\n" + p.to_string() + " : " + p.type() + ";\n");
            }
            for (auto s : input_state_set(*fa_)) {
                const auto& p = atl::get_property(*fa_, s);
                declaration_ += ("IVAR\n" + p.to_string() + " : " + p.type() + ";\n");
                //std::cout << declaration_ << std::endl;
            }
            return declaration_;
        }

        string& translate_initialization() {
            for (const auto& f : init_list(*fa_)) {
                initialization_ += "INIT\n" + f.to_string() + "\n";
            }
            return initialization_;
        }

        string& translate_transition() {
            transition_ += "ASSIGN\n";
            for (auto s : control_state_set(*fa_)) {
                const auto& p = atl::get_property(*fa_, s);
                transition_ += "next(" + p.to_string() + "):= case\n";
                typename fomula_automaton::OutTransitionIter it, end;
                for (tie(it, end) = out_transitions(*fa_, s); it != end; it++) {
                    auto t = atl::target(*fa_, *it);
                    transition_ += atl::get_property(*fa_, *it).to_string() + " : " +
                                   atl::get_property(*fa_, t).to_string() + ";\n";
                }
                transition_ += "esac;\n";
            }
            return transition_;
        }

        string& translate_specification(const string& type) {
            specification_ += type + " !(" + atl::get_property(*fa_).to_string() + ")";
            return specification_;
        }

        string translate_nuxmv_format(const string& type = "INVARSPEC") {
            return "MODULE main\n" +
                   translate_declaration() + 
                   translate_initialization() +
                   translate_transition() +
                   translate_specification(type);
        }

        const string& declaration() const {
            return declaration_;
        }

        const string& initialization() const {
            return initialization_;
        }

        const string& transition() const {
            return transition_;
        }

        const string& specification() const {
            return specification_;
        }
    private:
        fomula_automaton* fa_;
        string declaration_;
        string initialization_;
        string transition_;
        string specification_;
    };
}

#endif /* nuxmv_translator_hpp */
