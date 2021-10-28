//
// Created by james on 9/14/2021.
//

#include "LeftParenAutomaton.h"

void LeftParenAutomaton::S0(const std::string &input) {
    if (input[index] == '(') {
        inputRead = 1;
    }else{
        Serr();
    }
}