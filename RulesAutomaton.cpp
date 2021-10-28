//
// Created by james on 9/14/2021.
//

#include "RulesAutomaton.h"
void RulesAutomaton::S0(const std::string& input) {
    if (input[index] == 'R') {
        inputRead++;
        index++;
        Su(input);
    }
    else {
        Serr();
    }
}

void RulesAutomaton::Su(const std::string& input) {
    if (input[index] == 'u') {
        inputRead++;
        index++;
        Sl(input);
    }
    else {
        Serr();
    }
}
void RulesAutomaton::Sl(const std::string& input) {
    if (input[index] == 'l') {
        inputRead++;
        index++;
        Se(input);
    }
    else {
        Serr();
    }
}
void RulesAutomaton::Se(const std::string& input) {
    if (input[index] == 'e') {
        inputRead++;
        index++;
        Ss(input);
    }
    else {
        Serr();
    }
}

void RulesAutomaton::Ss(const std::string& input) {
    if (input[index] == 's') {
        inputRead++;
    }
    else {
        Serr();
    }
}