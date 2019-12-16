#include "str_solver.hpp"

int main(int argc, char* argv[]) {
    StrSolver solver((string(argv[1])));
    solver.solve(string(argv[2]));
    return 0;
}
