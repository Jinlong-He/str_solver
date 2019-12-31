#include "str_solver.hpp"

int main(int argc, char* argv[]) {
    cout << "Start solving..." << endl;
    StrSolver solver((string(argv[2])));
    if ((string(argv[1]) == "-1")) {
        solver.solve((string(argv[3])));
    } else if ((string(argv[1]) == "-I")) {
        solver.solve2((string(argv[3])), atoi(argv[4]), "cmd_file_ic3");
    } else if ((string(argv[1]) == "-F")) {
        solver.solve2((string(argv[3])), atoi(argv[4]), "cmd_file_bmc");
    }
    return 0;
}
