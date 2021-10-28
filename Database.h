//
// Created by james on 10/26/2021.
//

#ifndef DATABASE_H
#define DATABASE_H
#include<map>
#include<string>
#include "Relation.h"


class Database {
public:
    std::map<std::string, Relation*> data;
};


#endif //PROJECT1_DATABASE_H
