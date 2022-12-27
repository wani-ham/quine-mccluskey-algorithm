/*
===================================================================
"Computational Simulation of Quine-McCluskey Algorithm using C/C++"
        - Digital Logic Circuits, Yonsei university-
===================================================================
Date       | Author
11/30/2022 | Taewan Ham 
===================================================================
*/

#include <iostream>
#include <math.h>
#include <vector>
#include <set>
#include <string>
#include <algorithm>

using namespace std;

//variables
int num_of_var = 0;  // number of variables (4 or 5)
int num_of_min = 0;  // number of min-terms
bool bool_tmp = true;  // temporary variable for while loop in step 1
bool flag = true;  // temporary variable for while loop in step 2
int min_index = 0;  // index for vector minterm_list
int size_imp = 1;  // size of implicants in tmp_table
int l = 0;  // index number for qm_table and tmp_table
int u = 0;  // used
int g = 0;  // group
int f = 0;  // f in init_var4,5_table

// arrays
// size of the column of each table is fixed to 8 to use as parameter in functions
int init_table[32][8];
int init_4var_table[16][8] = {  // initial table of four variable minterms
  // A, B, C, D, g, u, f - g: group number, f: 0 or 1, u: used(1) not used(0)
	{0, 0, 0, 0, 0, 0, 0, 0},  //m0
	{0, 0, 0, 1, 1, 0, 0, 0},  //m1
	{0, 0, 1, 0, 1, 0, 0, 0},  //m2
	{0, 0, 1, 1, 2, 0, 0, 0},  //m3
	{0, 1, 0, 0, 1, 0, 0, 0},  //m4
	{0, 1, 0, 1, 2, 0, 0, 0},  //m5
	{0, 1, 1, 0, 2, 0, 0, 0},  //m6
	{0, 1, 1, 1, 3, 0, 0, 0},  //m7
	{1, 0, 0, 0, 1, 0, 0, 0},  //m8
	{1, 0, 0, 1, 2, 0, 0, 0},  //m9
	{1, 0, 1, 0, 2, 0, 0, 0},  //m10
	{1, 0, 1, 1, 3, 0, 0, 0},  //m11
	{1, 1, 0, 0, 2, 0, 0, 0},  //m12
	{1, 1, 0, 1, 3, 0, 0, 0},  //m13
	{1, 1, 1, 0, 3, 0, 0, 0},  //m14
	{1, 1, 1, 1, 4, 0, 0, 0},  //m15
};
int init_5var_table[32][8] = {  // initial table of five variable minterms
  // A, B, C, D, E, g, u, f - g: group number, f: 0 or 1, u: used(1) not used(0)
	{0, 0, 0, 0, 0, 0, 0, 0},  //m0
	{0, 0, 0, 0, 1, 1, 0, 0},  //m1
	{0, 0, 0, 1, 0, 1, 0, 0},  //m2
	{0, 0, 0, 1, 1, 2, 0, 0},  //m3
	{0, 0, 1, 0, 0, 1, 0, 0},  //m4
	{0, 0, 1, 0, 1, 2, 0, 0},  //m5
	{0, 0, 1, 1, 0, 2, 0, 0},  //m6
	{0, 0, 1, 1, 1, 3, 0, 0},  //m7
	{0, 1, 0, 0, 0, 1, 0, 0},  //m8
	{0, 1, 0, 0, 1, 2, 0, 0},  //m9
	{0, 1, 0, 1, 0, 2, 0, 0},  //m10
	{0, 1, 0, 1, 1, 3, 0, 0},  //m11
	{0, 1, 1, 0, 0, 2, 0, 0},  //m12
	{0, 1, 1, 0, 1, 3, 0, 0},  //m13
	{0, 1, 1, 1, 0, 3, 0, 0},  //m14
	{0, 1, 1, 1, 1, 4, 0, 0},  //m15
	{1, 0, 0, 0, 0, 1, 0, 0},  //m16
	{1, 0, 0, 0, 1, 2, 0, 0},  //m17
	{1, 0, 0, 1, 0, 2, 0, 0},  //m18
	{1, 0, 0, 1, 1, 3, 0, 0},  //m19
	{1, 0, 1, 0, 0, 2, 0, 0},  //m20
	{1, 0, 1, 0, 1, 3, 0, 0},  //m21
	{1, 0, 1, 1, 0, 3, 0, 0},  //m22
	{1, 0, 1, 1, 1, 4, 0, 0},  //m23
	{1, 1, 0, 0, 0, 2, 0, 0},  //m24
	{1, 1, 0, 0, 1, 3, 0, 0},  //m25
	{1, 1, 0, 1, 0, 3, 0, 0},  //m26
	{1, 1, 0, 1, 1, 4, 0, 0},  //m27
	{1, 1, 1, 0, 0, 3, 0, 0},  //m28
	{1, 1, 1, 0, 1, 4, 0, 0},  //m29
	{1, 1, 1, 1, 0, 4, 0, 0},  //m30
	{1, 1, 1, 1, 1, 5, 0, 0},  //m31
};
int tmp_table[32][8];  // table used in step 2
int qm_table[32][8];  // table used in step 2 (quine-mccluskey table)
int num_list[32] = { };  // number list (index : 0~31, initial value : 0)

// vectors
vector <int> vector_tmp;  // temporary vector
vector <int> epi;  // list of essential prime implicant
vector <vector <int>> minterm_list;  // list of minterms used in step 2
vector <vector <int>> tmp_minterm_list;  // list of minterms used in step 2
vector <vector <int>> final_minterm_list;  // final list of minterms (prime implicants)
vector <vector <int>> final_implicants;  // final list of implicants (prime implicants)

// functions
bool compare_digits(int arr[][8], int n, int m, int var_num);  // compare each two digits number (n & m)
void initialize_table(int arr[][8]);  // initialize elements of arr in to 0
void print_QM_op(int var_num);  // prints column info of qm operation in step 2
string binary_to_literal(vector <int> binary, int var_num);  // changes binary notation in to literal notation


int main(void) {	
	// ---- Step 1 : getting input from user ----
	while (bool_tmp) {  // getting number of variables
		printf("Please enter number of variables : ");
		scanf_s("%d", &num_of_var);  // input of number of variables (ex: 4, 5)
		if (num_of_var == 4 || num_of_var == 5) bool_tmp = false;
		else printf("Only 4 or 5 variables operation is available...\n");  // repeat until it gets the correct input
	}
	if (num_of_var == 4) {  // if variable is 4
		g = 4; u = 5; f = 6;  
		std::copy(&init_4var_table[0][0], &init_4var_table[0][0] + 16 * 8, &init_table[0][0]);
	}
	else {  // if variable is 5
		g = 5; u = 6; f = 7;
		std::copy(&init_5var_table[0][0], &init_5var_table[0][0] + 32 * 8, &init_table[0][0]);
	}
	
	bool_tmp = true;
	printf("\n");
	while (bool_tmp) {
		printf("Please enter number of min-terms : ");
		scanf_s("%d", &num_of_min);  // input of number of minterms (maximum: 2^(num_of_var)-1)
		if (num_of_var == 4 && num_of_min < 16) bool_tmp = 0;
		else if (num_of_var == 5 && num_of_min < 32) bool_tmp = 0;
		else printf("Please check your input again...\n");  // repeat until it gets the correct input
	}

	printf("\n");
	printf("Please enter minterms : ");
	for (int i = 0; i < num_of_min; i++) {  // getting minterms as input
		int tmp = 0;
		scanf_s("%d", &tmp); 
		init_table[tmp][f] = 1;  // update initial table 
	}

	// ---- Step 2 : Finding Prime implicants ----
	int cnt = 0;

	for (int i = 0; i < int(pow(2, num_of_var)); i++) {  //initializing qm_table with init_table
		if (init_table[i][f] == 1) {
			for (int j = 0; j < 8; j++) qm_table[l][j] = init_table[i][j];
			minterm_list.push_back(std::vector <int>());
			minterm_list[l].push_back(i);
			l++;
		}
	}

	while (flag) {
		int group = 0;
		int s = 0; // size of tmp_table
		flag = false;  // initialize flag
		size_imp *= 2;
		while (group < num_of_var) {  // operation (qm_table -> tmp_table)
			for (int i = 0; i < l; i++) {
				if (qm_table[i][f] == 1 && qm_table[i][g] == group) {
					for (int j = 0; j < l; j++) {
						if (qm_table[j][f] == 1 && qm_table[j][g] == group + 1) {
							if (compare_digits(qm_table, i, j, num_of_var)) {  // if two number satisfies the condition
								qm_table[i][u]++;  // check 'used'
								qm_table[j][u]++;
								bool fflag = false;
								//tmp_minterm_list.push_back(std::vector <int>());
								for (int n = 0; n < minterm_list[i].size(); n++) vector_tmp.push_back(minterm_list[i][n]); // record minterms
								for (int n = 0; n < minterm_list[j].size(); n++) vector_tmp.push_back(minterm_list[j][n]);
								sort(vector_tmp.begin(), vector_tmp.end());
								for (int n = 0; n < tmp_minterm_list.size(); n++) {
									std::set<vector<int>> s;
									s.insert(tmp_minterm_list[n]);
									auto rep = s.insert(vector_tmp);
									if (!rep.second) {  // if it is repeated
										fflag = true;
										break;
									}
								}
								if (!fflag) { // if it is not a repeated operation
									tmp_minterm_list.push_back(vector_tmp);
									sort(tmp_minterm_list[s].begin(), tmp_minterm_list[s].end());
									
									for (int k = 0; k < num_of_var; k++) {
										if (qm_table[i][k] == qm_table[j][k]) tmp_table[s][k] = qm_table[i][k];
										else tmp_table[s][k] = -1;
									}
									tmp_table[s][f] = 1;
									tmp_table[s][g] = group;

									s++;
									flag = true;  // flag is false if there is no available combining
								}
								vector_tmp.clear();
							}
						}
					}
				}
			}
			group++;
		}
		for (int i = 0; i < l; i++) {  // find prime implicants
			if (qm_table[i][f] == 1 && qm_table[i][u] == 0) {
				final_minterm_list.push_back(minterm_list[i]);
				for (int j = 0; j < num_of_var; j++) {
					vector_tmp.push_back(qm_table[i][j]);
				}
				final_implicants.push_back(vector_tmp);
			}
			vector_tmp.clear();
		}

		// print each stage of operation
		printf("\n----QM operation----\n");
		print_QM_op(num_of_var);
		for (int q = 0; q < l; q++) {
			for (int w = 0; w < 8; w++) printf("%d ", qm_table[q][w]);
			printf("||| m( ");
			for (int e = 0; e < minterm_list[q].size(); e++)  printf("%d ", minterm_list[q][e]);
			printf(")\n");
		}

		// qm reset, qm = tmp, tmp reset
		initialize_table(qm_table);
		std::copy(&tmp_table[0][0], &tmp_table[0][0] + s * 8, &qm_table[0][0]);
		initialize_table(tmp_table);

		// minterm_list reset, min = tmp, tmp reset
		minterm_list.assign(tmp_minterm_list.size(), std::vector<int>(tmp_minterm_list.size()));
		std::copy(tmp_minterm_list.begin(), tmp_minterm_list.end(), minterm_list.begin());
		tmp_minterm_list.assign(0, std::vector<int>(0));

		// initialize index values
		l = s;
		s = 0;  // initializing size of qm_table
	}

	// ---- Step 3: Prime Implicant Chart ----
	int pi_num = final_minterm_list.size();  // number of rows of the prime implicant chart
	std::vector <int> col_chart;  // column of the prime implicant chart

	// printing prime implicants
	printf("\n----List of Prime Implicants----\n");
	for (int i = 0; i < pi_num; i++) {
		printf("m( ");
		for (int j = 0; j < final_minterm_list[i].size(); j++) {
			printf("%d ", final_minterm_list[i][j]);
			num_list[final_minterm_list[i][j]]++;  // count how many time the min-term is included in prime implicants
		}
		printf(")\n");
	}

	//  make a vector that contains min-term list 
	for (int i = 0; i < 32; i++) {
		if (num_list[i] != 0) {
			col_chart.push_back(i);
		}
	}


	int col_size = col_chart.size();  
	std::vector< vector <int>> pi_chart;  // prime implicant chart

	// creating prime implicant chart (pi_chart)
	for (int i = 0; i < pi_num; i++) {
		bool fflag = true;  // flag for epi
		for (int j = 0; j < col_size; j++) {
			bool fflag_ = true;  // flag for pushing back 0 in pi_chart
			for (int k = 0; k < final_minterm_list[i].size(); k++) {
				if (final_minterm_list[i][k] == col_chart[j]) {
					vector_tmp.push_back(num_list[col_chart[j]]);  // num_list[col_chart[j]] is equal to the frequency of min-term
					if (num_list[col_chart[j]] == 1 && fflag == true) {
						epi.push_back(i);  // essential prime implicant
						fflag = false;  // prevent repeat of same epi value
					}
					fflag_ = false;
				}
			}	
			if(fflag_) vector_tmp.push_back(0);  // push 0 if there is a number in col_chart[] but not in final_minterm_list[][]
		}
		pi_chart.push_back(vector_tmp);
		vector_tmp.clear();
	}

	printf("\n----Prime Implicants Chart----\n");
	for (int i = 0; i < col_size; i++) printf("%d ", col_chart[i]);  // print column info (which is list of min-terms
	printf("\n------------------------------\n");
	for (int i = 0; i < pi_num; i++) {  // print prime implicant chart
		for (int j = 0; j < col_size; j++) {
			printf("%d ", pi_chart[i][j]);
		}
		printf("\n");
	}

	printf("\n----Essential Prime Implicants----\n");
	for (int i = 0; i < epi.size(); i++) {  // print essential prime implicants
		string str_tmp = binary_to_literal(final_implicants[epi[i]], num_of_var);
		for(int j = 0; j < str_tmp.size(); j++) printf("%c", str_tmp[j]); //  print literals
		printf("\n");
	}

	return 0;
}

bool compare_digits(int arr[][8], int n, int m, int var_num) {
	int result = 0;
	for (int i = 0; i < var_num; i++) {
		if (arr[n][i] != arr[m][i]) result++;
	}
	if (result == 1) return true;  // if n, m have only one digit in common return true
	else return false;
}

void initialize_table(int arr[][8]) {
	for (int i = 0; i < 32; i++) {
		for (int j = 0; j < 8; j++) arr[i][j] = 0;
	}
}

void print_QM_op(int var_num) {
	for (int i = 0; i < var_num; i++) printf("%c ", 65 + i);
	printf("g u f");  // group, used, f
	printf("\n--------------------\n");
}


string binary_to_literal(vector <int> binary, int var_num) {
	char l_tmp;  // literal
	char c_tmp;  // asterisk
	string str_tmp;  //  output variable
	for (int i = 0; i < var_num; i++) {
		if (binary[i] == 1) {
			l_tmp = char(i + 65);  // change it to literal
			str_tmp += l_tmp;
		}
		else if (binary[i] == 0) {
			l_tmp = char(i + 65);  // change it to literal
			str_tmp += l_tmp;
			str_tmp.push_back(char(39));  // add asterisk (using ascii code)
		}
	}
	return str_tmp;
}
