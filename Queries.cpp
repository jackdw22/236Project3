//
// Created by james on 9/14/2021.
//

#include "Queries.h"
void Queries::S0(const std::string& input) {
    if (input[index] == 'Q') {
        inputRead++;
        index++;
        Su(input);
    }
    else {
        Serr();
    }
}

void Queries::Su(const std::string& input) {
    if (input[index] == 'u') {
        inputRead++;
        index++;
        Se(input);
    }
    else {
        Serr();
    }
}

void Queries::Se(const std::string& input) {
    if (input[index] == 'e') {
        inputRead++;
        index++;
        Sr(input);
    }
    else {
        Serr();
    }
}

void Queries::Sr(const std::string& input) {
    if (input[index] == 'r') {
        inputRead++;
        index++;
        Si(input);
    }
    else {
        Serr();
    }
}
void Queries::Si(const std::string& input) {
    if (input[index] == 'i') {
        inputRead++;
        index++;
        Se2(input);
    }
    else {
        Serr();
    }
}
void Queries::Se2(const std::string& input) {
    if (input[index] == 'e') {
        inputRead++;
        index++;
        Ss(input);
    }
    else {
        Serr();
    }
}

void Queries::Ss(const std::string& input) {
    if (input[index] == 's') {
        inputRead++;
    }
    else {
        Serr();
    }
}


