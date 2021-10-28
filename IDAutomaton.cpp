//
// Created by james on 9/14/2021.
//

#include "IDAutomaton.h"
#include <ctype.h>
#include <iostream>

void IDAutomaton::S0(const std::string& input) {
    if (isalpha(input[index])) {
        inputRead++;
        index++;
        S1(input);
    }
    else {
        Serr();
    }
}

void IDAutomaton::S1(const std::string& input) {
    while (isalpha(input[index]) || isdigit(input[index])) {
        inputRead++;
        index++;

    }
    }



