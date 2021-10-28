//
// Created by james on 9/15/2021.
//

#include "BlockCommentAutomata.h"
void BlockCommentAutomata::S0(const std::string &input) {
    if (input[index] == '#'){
        inputRead++;
        index++;
        S1(input);
    }else{
        Serr();
    }
}

void BlockCommentAutomata::S1(const std::string &input) {
    if(input[index] == '|'){
        inputRead++;
        index++;
        S2(input);
    }else{
        Serr();
    }

}

void BlockCommentAutomata::S2(const std::string &input) {
    while(input[index] != '|'){
        inputRead++;
        index++;
        if(input[index] == '\n'){
            newLines++;
        }if(static_cast<int>(input.size()) == inputRead){
            Serr();
        }
    }S3(input);

}


void BlockCommentAutomata::S3(const std::string &input) {
    if(input[index] == '|'){
        inputRead++;
        index++;
        S4(input);
    }else{
        Serr();
    }

}

void BlockCommentAutomata::S4(const std::string &input) {
    if(input[index] == '#'){
        inputRead++;
    }else{
        Serr();
    }

}


