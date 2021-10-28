//
// Created by james on 9/15/2021.
//

#include "InvalidStringAutomaton.h"
void InvalidStringAutomaton::S0(const std::string &input) {
    if (input[index] == '\''){
        inputRead++;
        index++;
        S1(input);
    }else{
        Serr();
    }
}

void InvalidStringAutomaton::S1(const std::string &input) {
    if (input[index] == '\''){
        Serr();
        return;
    }
    for (int i = index; i < static_cast<int>(input.size()); i++) {
        if (input.at(i) == '\'') {
            if(static_cast<int>(input.size()) == i + 1){
                Serr();
                break;
            }
            else if (input.at(i + 1) != '\'' && input.at(i - 1) != '\'') {
                Serr();
                break;
            }
        }
        if (input[index] == '\n') {
            newLines++;
        }
            inputRead++;
            index++;

            if (static_cast<int>(input.size()) == inputRead) {
                break;
            }

        }
        // if(input[index] == '\''){
        //     Serr();
        //   }
    }

