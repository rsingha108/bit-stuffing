#include <iostream>
#include <chrono>
#include <random>

using namespace std;
using namespace std::chrono;

// Function to print a bit vector
void print_bits(unsigned long bits, int size) {
    for (int i = size - 1; i >= 0; --i) {
        cout << ((bits >> i) & 1) << " ";
    }
    cout << endl;
}

std::pair<unsigned long, int> add_flags(unsigned long a, unsigned long f, int a_size, int f_size) {
    return std::make_pair((f << (a_size + f_size)) | (a << f_size) | f, a_size + 2 * f_size);
}

std::pair<unsigned long, int> remove_flags(unsigned long a, unsigned long f, int a_size, int f_size) {
    unsigned long mask = ((1UL << a_size) - 1) << f_size;
    return std::make_pair((a & mask) >> f_size, a_size - 2 * f_size);
}

std::pair<unsigned long, int> stuff(unsigned long a, unsigned long k, bool s, int a_size, int k_size) {
    unsigned long result = a;
    unsigned long mask;
    int r_size = a_size;
    for (int i = 0; i <= r_size - k_size;) {
        mask = k << (r_size-k_size-i);
        // cout << "result       : "; print_bits(result, r_size);
        // cout << "mask         : "; print_bits(mask,r_size);
        // cout << "result & mask: ";  print_bits(result & mask, r_size);
        // cout << "k shifted    : "; print_bits(k << (r_size - k_size - i), r_size);
        if ((result & mask) == (k << (r_size - k_size - i))) {
            // cout << "match!" << endl;
            // cout << "result       : "; print_bits(result, r_size);
            unsigned long before_kernel = result >> (r_size - i);
            // cout << "bef kernel   : "; print_bits(before_kernel, i);
            unsigned long after_kernel = result & ((1UL << (r_size-i-k_size)) - 1);
            // cout << "aft kernel   : "; print_bits(after_kernel, r_size - i - k_size);
            result = (before_kernel << (r_size-i+1)) | (k << (r_size-i-k_size+1)) | (s << (r_size-i-k_size)) | after_kernel;
            r_size++;
            // cout << "result       : "; print_bits(result, r_size);
            i = i + k_size + 1;
        }
        else {
            // cout << "no match!" << endl;
            ++i;
        }
    }

    return std::make_pair(result, r_size);
}


std::pair<unsigned long, int> destuff(unsigned long b, unsigned long k, bool s, int b_size, int k_size) {
    unsigned long result = b;
    unsigned long mask;
    int r_size = b_size;
    unsigned long k_orig = k;
    // update k to include the stuffing bit
    k = (k << 1) | s;
    // cout << "result      : "; print_bits(result, r_size);
    for (int i = 0; i <= r_size - k_size;) {
        mask = k << (r_size - k_size - i);

        // Check if the current segment matches the stuffed pattern
        if (((result & mask) == (k << (r_size - k_size - i)))) {
            // Perform destuffing operation
            unsigned long before_kernel = result >> (r_size - i);
            unsigned long after_kernel = result & ((1UL << (r_size - i - k_size)) - 1);
            result = (before_kernel << (r_size-i-1)) | (k_orig << (r_size-i-k_size-1)) | after_kernel;
            r_size--;
            // cout << "result      : "; print_bits(result, r_size);
            i = i + k_size;
        }
        else {
            ++i;
        }
    }

    return std::make_pair(result, r_size);
}

int main() {
    // Generate random bits
    int n = 16;

    unsigned long k = 0b11; // kernel pattern: 11
    unsigned long f = 0b01110; // flag pattern: 01110
    bool s = false; // stuffing bit 0

    unsigned long a = 49055;
    auto p = stuff(a, k, s, n, 2);
    auto p1 = add_flags(p.first, f, p.second, 5);
    auto p2 = remove_flags(p1.first, f, p1.second, 5);
    auto p3 = destuff(p2.first, k, s, p2.second, 2);
    cout << "Original    : "; print_bits(a, n);
    cout << "Stuffed     : "; print_bits(p.first, p.second);
    cout << "With flags  : "; print_bits(p1.first, p1.second);
    cout << "W/o flags   : "; print_bits(p2.first, p2.second);
    cout << "Destuffed   : "; print_bits(p3.first, p3.second);
    // cout << "Destuffed   : "; print_bits(q.first, q.second);

    auto start = high_resolution_clock::now();
    for (int i=0;i<10000000;i++){
        p = stuff(a, k, s, n, 2);
        p1 = add_flags(p.first, f, p.second, 5);
        p2 = remove_flags(p1.first, f, p1.second, 5);
        p3 = destuff(p2.first, k, s, p2.second, 2);
    }
    auto stop = high_resolution_clock::now(); 

    auto duration = duration_cast<microseconds>(stop - start);
    cout << "Time Taken : " << duration.count() << endl;

    return 0;
}
