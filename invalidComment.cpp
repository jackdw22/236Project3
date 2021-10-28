//
// Created by james on 9/15/2021.
//

#include <iostream>
#include "invalidComment.h"
void invalidComment::S0(const std::string &input) {
        if (input[index] == '#'){
            inputRead++;
            index++;
            S1(input);
        }else{
            Serr();
        }
}

void invalidComment::S1(const std::string &input) {
    if(input[index] == '|'){
        inputRead++;
        index++;
        S2(input);
    }else{
        Serr();
    }

}

void invalidComment::S2(const std::string &input) {
    while(input[index] != '|') {
        if (input[index] == '\n') {
            newLines++;
        }
        inputRead++;
        index++;
        if (static_cast<int>(input.size()) == inputRead) {
            break;
        }
    }if(input[index] == '|'){
       if (static_cast<int>(input.size()) == inputRead){
           return;
       }else if(input[index + 1] == '#'){
           Serr();
       }else{
           inputRead++;
           index++;
           S2(input);
       }
    }

}