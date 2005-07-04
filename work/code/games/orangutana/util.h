#ifndef __UTIL_H__
#define __UTIL_H__

#include <string>
#include <sstream>

using std::string;

class Exception
{
public:
    Exception(const string& msg) : msg(msg) { }
    ~Exception() throw() { }

    string message() const { return msg; }
private:
    string msg;
};

int _die(const string& msg, const char* file, int line) 
{
    std::stringstream ss;
    ss << msg << " at " << file << " line " << line;
    throw Exception(ss.str());
}

#define DIE(msg) _die(string() + msg, __FILE__, __LINE__)

#endif
