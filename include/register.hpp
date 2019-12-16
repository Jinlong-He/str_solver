//
//  register.hpp
//
//  Created by Jinlong He on 2019/12/08.
//  Copyright © 2019年 Jinlong He. All rights reserved.
//

#ifndef register_hpp 
#define register_hpp
#include <vector>
#include <boost/algorithm/string.hpp>
#include "../../fml/atl/automaton/finite_automaton/nondeterministic_finite_automaton.hpp"
using std::vector;

class RegisterNames {
public:
    typedef vector<string> strings;

    RegisterNames() {}

    RegisterNames(const strings& names) 
        : names_(names) {}

    RegisterNames(const string& names, const string& x = ";") {
        boost::split(names_, names, boost::is_any_of(x));
    }

    const strings& names() const {
        return names_;
    }

    bool operator==(const RegisterNames& r) const {
        return names_ == r.names_;
    }

    RegisterNames operator&(const RegisterNames& r) const {
        strings strs(names_);
        strs.insert(strs.end(), r.names_.begin(), r.names_.end());
        return RegisterNames(strs);
    }

    friend std::ostream& operator<< (std::ostream& os, const RegisterNames& r) {
        for (const auto& name : r.names_) {
            os << name << " ";
        }
        return os;
    }
private:
    strings names_;
};

class Registers {
public:
    typedef vector<int> ints;
    Registers() {}

    Registers(const ints& nums)
        : nums_(nums) {}

    Registers(long l) 
        : nums_(1) {
            nums_[0] = l;
        }

    const ints& nums() const {
        return nums_;
    }

    string to_string() const {
        string res = "r_";
        for (auto n : nums_) {
            res += std::to_string(n) + "_";
        }
        return res;
    }

    bool operator==(const Registers& r) const {
        return nums_ == r.nums_;
    }

    Registers operator&(const Registers& r) const {
        ints ns(nums_);
        ns.insert(ns.end(), r.nums_.begin(), r.nums_.end());
        return Registers(ns);
    }

    friend std::ostream& operator<< (std::ostream& os, const Registers& r) {
        for (const auto& num : r.nums_) {
            os << num << " ";
        }
        return os;
    }
private:
    ints nums_;
};

namespace boost {
    template <>
    struct boost::hash<Registers> {
        std::size_t operator()(const Registers& r) const {
            return boost::hash_value(r.nums());
        }
    };

    template <>
    struct boost::hash<RegisterNames> {
        std::size_t operator()(const RegisterNames& r) const {
            return boost::hash_value(r.names());
        }
    };
}
#endif /* register_hpp */
