#include<bits/stdc++.h>
#include<vector>
#include<chrono>

using namespace std;
using namespace std::chrono;

void print(vector<bool> v){
    for (auto i : v){
        cout << i << " ";
    }
    cout << endl;
}

vector<bool> stuff(vector<bool> a, vector<bool> k , bool s){
    for (unsigned i = 0; i <= a.size() - k.size() ; )
    {
        vector<bool> v(a.begin()+i,a.begin()+i+k.size()); //print(v);
        if (v == k){
            a.insert(a.begin()+i+k.size(),s);
            i = i+k.size()+1;
        }
        else{
            ++i;
        }
    }
    return a;
}

vector<bool> destuff(vector<bool> b, vector<bool> k , bool s){
    for (unsigned i = 0; i <= b.size() - k.size() ; )
    {
        vector<bool> v(b.begin()+i,b.begin()+i+k.size()); //print(v);
        if (v == k){
            if (b[i+k.size()] == s){
                b.erase(b.begin()+i+k.size());
                i = i+k.size();
            }
        }
        else{
            ++i;
        }
    }
    return b;
}

vector<bool> add_flags(vector<bool> a, vector<bool> f){
    vector<bool> v(f);
    v.insert(v.end(), a.begin(), a.end());
    v.insert(v.end(),f.begin(),f.end());
    return v;
}

vector<bool> rem_flags(vector<bool> a, vector<bool> f){
    vector<bool> v1(a.begin(),a.begin()+f.size()); 
    vector<bool> v2(a.end()-f.size(),a.end()); 
    //cout << "v1 : ";print(v1);
    //cout << "v2 : ";print(v2);
    if (v1 == f && v2 == f) {
        a.erase(a.begin(),a.begin()+f.size());
        a.erase(a.end()-f.size(),a.end());
    } 
    return a;
}

vector<bool> generate_random_bits(int n) {
    vector<bool> result;
    random_device rd;   // obtain a random number from hardware
    mt19937 gen(rd());  // seed the generator
    uniform_int_distribution<> distrib(0, 1); // define the range

    for (int i = 0; i < n; ++i) {
        bool bit = distrib(gen);  // generate a random bit (0 or 1)
        result.push_back(bit);
    }

    return result;
}


int main(){

    vector<bool> a; 
    //int arr[] = {1,0,0,1,0};
    // bool arr[] = {true,false,false,true,false};
    // for (auto i : arr) {a.push_back(i);}
    a = generate_random_bits(12000);


    vector<bool> k; 
    //int arr1[] = {1,1}; --> kernel
    bool arr1[] = {true,true};
    for (auto i : arr1) {k.push_back(i);}

    vector<bool> f; 
    //int arr2[] = {0,1,1,1,0}; --> flag
    bool arr2[] = {false,true,true,true,false};
    for (auto i : arr2) {f.push_back(i);}

    bool s = true;

    vector<bool> b;
    vector<bool> b1; 
    vector<bool> b2 ; 
    vector<bool> b3;

    auto start = high_resolution_clock::now();
    for (int i=0;i<1000;i++){
        // b = stuff(a,k,s);
        // b1 = add_flags(b,f); 
        // b2 = rem_flags(b1,f); 
        // b3 = destuff(b2,k,s);
        b = add_flags(a,f);
        b1 = rem_flags(b,f);
    }
    auto stop = high_resolution_clock::now(); 

    auto duration = duration_cast<microseconds>(stop - start);
    cout << "Time Taken : " << duration.count() << endl;

    // cout << "a : "; print(a);
    // cout << "k : "; print(k);
    // cout << "s : " << s << endl;
    // cout << "f : "; print(f);
    // cout << "b : "; print(b);
    // cout << "b1 : "; print(b1);
    // cout << "b2 : "; print(b2);
    // cout << "b3 : "; print(b3);
}
