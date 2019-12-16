#include "idcra_parser.hpp"
void IdcraParser::parse(const vector<string>& strs, IDCRA& idcra) {
    vector<string> states_strs, init_strs, final_strs, final_num_strs, trans_strs, reg_strs, reg_name_strs;
    unordered_set<int> final_nums;
    boost::split(states_strs, strs[0], boost::is_any_of(":"));
    boost::split(init_strs, strs[1], boost::is_any_of(":"));
    boost::split(final_strs, strs[2], boost::is_any_of(":"));
    boost::split(reg_name_strs, strs[strs.size() - 1], boost::is_any_of(":"));
    size_t length = final_strs[1].find_last_of(",");
    boost::split(final_num_strs, final_strs[1].substr(0,length), boost::is_any_of(","));
    int states_num = atoi(states_strs[1].c_str());
    int init_num = atoi(init_strs[1].c_str());
    //cout << "final" << final_strs[1].substr(0,length) << endl;
    for (auto& str : final_num_strs) {
        //cout <<  atoi(str.c_str())<< endl;
        final_nums.insert(atoi(str.c_str()));
    }
    for (int i = 0; i < states_num; i++) {
        add_state(idcra);
        if (i == init_num) {
            idcra.set_initial_state(i);
        } 
        if (final_nums.count(i) > 0) {
            idcra.set_final_state(i);
        }
    }
    size_t reg_length = reg_name_strs[1].find_last_of(";") - 1;
    RegisterNames register_names(reg_name_strs[1].substr(1, reg_length));
    if (reg_name_strs[1].length() > 2) {
    //cout << "name: " << reg_name_strs[1].substr(1, reg_length) <<endl;
        atl::set_property(idcra, register_names);
    }
    for (ID i = 4; i < strs.size() - 1; i++) {
        trans_strs.clear();
        reg_strs.clear();
        boost::split(trans_strs, strs[i], boost::is_any_of(";"));
        boost::split(reg_strs, trans_strs[4].substr(5, trans_strs[4].length() - 6), boost::is_any_of(","));
        int source = atoi(trans_strs[0].c_str());
        int target = atoi(trans_strs[1].c_str());
        int min = atoi(trans_strs[2].c_str());
        int max = atoi(trans_strs[3].c_str());
        vector<int> nums;
        for (auto& reg : reg_strs) {
            nums.push_back(atoi(reg.c_str()));
        }
        Registers registers(nums);
        if (reg_name_strs[1].size() > 2) {
            atl::add_transition(idcra, source, target, Label(min, max), registers);
        } else {
            atl::add_transition(idcra, source, target, Label(min, max), Registers());
        }
    }
}

