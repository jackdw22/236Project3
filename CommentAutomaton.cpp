//
// Created by james on 9/15/2021.
//

#include "CommentAutomaton.h"
void CommentAutomaton::S0(const std::string &input) {
    if (input[index] == '#'){
        inputRead++;
        index++;
        S1(input);
    }else{
        Serr();
    }
}


void CommentAutomaton::S1(const std::string &input) {
    if (input[index] == '|') {
        Serr();
    }else{
        while(input[index] != '\n') {
            inputRead++;
            index++;
            if (static_cast<int>(input.size()) == inputRead){
                break;
            }
        }

    }
}
