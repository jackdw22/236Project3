//
// Created by james on 9/14/2021.
//

#include "schemesAutomaton.h"
void schemesAutomaton::S0(const std::string &input) {
    if(input[index] == 'S'){
        inputRead++;
        index++;
        Sc(input);
    }else{
        Serr();
    }
}

void schemesAutomaton::Sc(const std::string &input) {
    if(input[index] == 'c'){
        inputRead++;
        index++;
       Sh(input);
    }else{
        Serr();
    }
}

void schemesAutomaton::Sh(const std::string &input) {
    if(input[index] == 'h'){
        inputRead++;
        index++;
        Se1(input);
    }else{
        Serr();
    }
}

void schemesAutomaton::Se1(const std::string &input) {
    if(input[index] == 'e'){
        inputRead++;
        index++;
        Sm(input);

    }else{
        Serr();
    }
}

void schemesAutomaton::Sm(const std::string &input) {
    if(input[index] == 'm'){
        inputRead++;
        index++;
        Se2(input);
    }else{
        Serr();
    }
}

void schemesAutomaton::Se2(const std::string &input) {
    if(input[index] == 'e'){
        inputRead++;
        index++;
        Ss(input);

    }else{
        Serr();
    }
}

void schemesAutomaton::Ss(const std::string &input) {
    if(input[index] == 's'){
        inputRead++;
    }else{
        Serr();
    }
}
