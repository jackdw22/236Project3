//
// Created by james on 10/26/2021.
//

#ifndef TUPLE_H
#define TUPLE_H
#include <vector>
#include <string>


class Tuple {

public:

    bool operator<(const Tuple &rhs) const {
        return values < rhs.values;
    }
    /*

    bool operator>(const Tuple &rhs) const {
        return rhs < *this;
    }

    bool operator<=(const Tuple &rhs) const {
        return !(rhs < *this);
    }


    bool operator>=(const Tuple &rhs) const {
        return !(*this < rhs);
    }
     */

    std::vector<std::string> values;
};


#endif //PROJECT1_TUPLE_H
