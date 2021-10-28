//
// Created by james on 9/29/2021.
//

#ifndef PARAMETER_H
#define PARAMETER_H
#include <string>
#include <iostream>


class Parameter {
private:
    std::string para;

public:
    Parameter(std::string para);
    std::string getParameter();
    bool isConstant();
};


#endif //PARAMETER_H
