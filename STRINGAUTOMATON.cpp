//
// Created by james on 9/15/2021.
//

#include "STRINGAUTOMATON.h"
void StringAutomaton::S0(const std::string &input) {
    if (input[index] == '\''){
        inputRead++;
        index++;
        S1(input);
    }else{
        Serr();
    }
}

void StringAutomaton::S1(const std::string &input) {
    if (input[index] == '\'' && input[index + 1] != '\''){
        inputRead++;
        index++;
        return;
    }
    while(input[index] != '\''){
        if(input[index] == '\n') {
            newLines++;
        }
        inputRead++;
        index++;
        if(static_cast<int>(input.size()) == inputRead){
            Serr();
            break;
        }
    }
    S2(input);
}

void StringAutomaton::S2(const std::string &input){
    if (input[index] == '\'') {
        if (input[index + 1] == '\''){
            inputRead += 2;
            index += 2;
            S1(input);
        }else{
            inputRead++;
        }
    }else{
        Serr();
    }

}