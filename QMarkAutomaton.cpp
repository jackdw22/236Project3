//
// Created by james on 9/14/2021.
//

#include "QMarkAutomaton.h"

void QMarkAutomaton::S0(const std::string &input) {
    if(input[index] == '?'){
        inputRead = 1;
    }else{
        Serr();
    }
}