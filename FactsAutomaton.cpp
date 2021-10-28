//
// Created by james on 9/14/2021.
//

#include "FactsAutomaton.h"
void FactsAutomaton::S0(const std::string &input) {
    if (input[index] == 'F') {
        inputRead++;
        index++;
        Sa(input);
    }
    else {
        Serr();
    }
}

void FactsAutomaton::Sa(const std::string &input) {
    if (input[index] == 'a') {
        inputRead++;
        index++;
        Sc(input);
    }
    else {
        Serr();
    }
}

void FactsAutomaton::Sc(const std::string &input) {
    if (input[index] == 'c') {
        inputRead++;
        index++;
        St(input);
    }
    else {
        Serr();
    }
}

void FactsAutomaton::St(const std::string &input) {
    if (input[index] == 't') {
        inputRead++;
        index++;
        Ss(input);
    }
    else {
        Serr();
    }
}

void FactsAutomaton::Ss(const std::string &input) {
    if (input[index] == 's') {
        inputRead++;
    }
    else {
        Serr();
    }
}



