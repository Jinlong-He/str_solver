//
//  label.hpp
//
//  Created by Jinlong He on 2019/12/08.
//  Copyright © 2019年 Jinlong He. All rights reserved.
//

#ifndef label_hpp 
#define label_hpp
#include <map>
#include "../fml/atl/automaton/finite_automaton/nondeterministic_finite_automaton.hpp"

class Label {
public:
    Label()
        : min_(0),
          max_(0) {}

    Label(long l) 
        : min_(l),
          max_(l) {}


    Label(int min, int max)
        : min_(min),
          max_(max) {}

    std::size_t hash_value() const {
        return ((std::hash<int>()(min_)) ^
                (std::hash<int>()(max_)));
    }

    int min() const {
        return min_;
    }

    int max() const {
        return max_;
    }

    bool operator==(const Label& label) const {
        return min_ == label.min_ && 
               max_ == label.max_;
    }

    friend std::ostream& operator<< (std::ostream& os, const Label& l) {
        os << l.min_ << ", " << l.max_;
        return os;
    }

    string to_string() const {
        return "l_" + std::to_string(min_) + "_" + std::to_string(max_);
    }
private:
    int min_;
    int max_;
};

namespace boost {
    template <>
    struct hash<Label> {
        std::size_t operator()(const Label& l) const {
            return l.hash_value();
        }
    };
}

#endif /* incra_hpp */
