#include <iostream>
#include <cstring>
#include <cstdlib>
#include <ctime>
#include <chrono>
using namespace std;
using namespace std::chrono;

// Function to add flags to the frame
int* addFlags(const int* frame, int frameSize, const int* flag, int flagSize, int& newSize) {
    // Calculate the new size
    newSize = frameSize + 2 * flagSize;

    // Create a new array to store the framed data with flags
    int* framedData = new int[newSize];

    // Add the starting flag
    memcpy(framedData, flag, flagSize * sizeof(int));

    // Add the original data
    memcpy(framedData + flagSize, frame, frameSize * sizeof(int));

    // Add the ending flag
    memcpy(framedData + flagSize + frameSize, flag, flagSize * sizeof(int));

    return framedData;
}

// Function to remove flags from the frame
int* removeFlags(const int* frame, int frameSize, const int* flag, int flagSize, int& newSize) {
    // Check if the frame starts with the flag and remove it
    if (memcmp(frame, flag, flagSize * sizeof(int)) == 0) {
        frame += flagSize;
        frameSize -= flagSize;
    }

    // Check if the frame ends with the flag and remove it
    if (memcmp(frame + frameSize - flagSize, flag, flagSize * sizeof(int)) == 0) {
        frameSize -= flagSize;
    }

    // Create a new array to store the frame without flags
    int* unframedData = new int[frameSize];
    memcpy(unframedData, frame, frameSize * sizeof(int));

    // Update the new size
    newSize = frameSize;

    return unframedData;
}

// Function for bit stuffing
int* bitStuffing(const int* arr, int N, int& stuffedSize) {
    // Create an array large enough to store the stuffed bits
    int* stuffedArr = new int[N * 2]; // Assuming a worst case where every 5 consecutive 1's needs stuffing

    // Variables to traverse arrays
    int i = 0, j = 0;

    // Loop to traverse in the range [0, N)
    while (i < N) {
        if (arr[i] == 1) {
            // Insert the 1 and check for consecutive ones
            stuffedArr[j++] = arr[i];
            int count = 1;

            // Check for the next 5 bits
            for (int k = i + 1; k < N && arr[k] == 1 && count < 5; k++) {
                stuffedArr[j++] = arr[k];
                count++;
                i = k;

                // If 5 consecutive set bits are found, insert a 0 bit
                if (count == 5) {
                    stuffedArr[j++] = 0;
                    break;
                }
            }
        } else {
            // Insert 0 bits
            stuffedArr[j++] = arr[i];
        }
        i++;
    }

    // Update stuffed size
    stuffedSize = j;

    // Create a trimmed array with the exact stuffed size
    int* finalStuffedArr = new int[stuffedSize];
    memcpy(finalStuffedArr, stuffedArr, stuffedSize * sizeof(int));
    delete[] stuffedArr;

    return finalStuffedArr;
}

// Function for bit destuffing
int* bitDestuffing(const int* arr, int N, int& destuffedSize) {
    // Create an array to store the destuffed bits
    int* destuffedArr = new int[N];

    // Variables to traverse arrays
    int i = 0, j = 0;

    // Loop to traverse in the range [0, N)
    while (i < N) {
        if (arr[i] == 1) {
            // Insert the 1 and check for consecutive ones
            destuffedArr[j++] = arr[i];
            int count = 1;

            // Check for the next 5 bits or until the end of the array
            for (int k = i + 1; k < N && arr[k] == 1; k++) {
                count++;
                i = k;
                destuffedArr[j++] = arr[k];

                // If 5 consecutive 1's are found, skip the next 0
                if (count == 5 && (i + 1) < N && arr[i + 1] == 0) {
                    i++; // Skip the zero after five consecutive 1's
                    break;
                }
            }
        } else {
            // Insert 0 bits
            destuffedArr[j++] = arr[i];
        }
        i++;
    }

    // Update destuffed size
    destuffedSize = j;

    // Create a trimmed array with the exact destuffed size
    int* finalDestuffedArr = new int[destuffedSize];
    memcpy(finalDestuffedArr, destuffedArr, destuffedSize * sizeof(int));
    delete[] destuffedArr;

    return finalDestuffedArr;
}

// Function to generate a random integer array of length N with 0 and 1 values
int* generate_random_array(int N) {
    srand(time(0));
    int* arr = new int[N];
    for (int i = 0; i < N; i++) {
        arr[i] = rand() % 2;
    }
    return arr;
}

void measure_time(int n_iterations, const int* flag, int flagSize, int dataSize) {

    // Variables for result sizes
    int stuffedSize, framedSize, unframedSize, destuffedSize;

    // Measure the time over the given number of iterations
    auto start = high_resolution_clock::now();

    // Generate a random data array
    int* data = generate_random_array(dataSize);

    for (int i = 0; i < n_iterations; i++) {
        // Step 1: Apply bit stuffing
        int* stuffedData = bitStuffing(data, dataSize, stuffedSize);

        // Step 2: Add flags to the stuffed data
        int* framedData = addFlags(stuffedData, stuffedSize, flag, flagSize, framedSize);

        // Step 3: Remove flags from the framed data
        int* unframedData = removeFlags(framedData, framedSize, flag, flagSize, unframedSize);

        // Step 4: Apply bit destuffing
        int* destuffedData = bitDestuffing(unframedData, unframedSize, destuffedSize);
    }

    auto end = high_resolution_clock::now();

    // Calculate the elapsed time
    auto duration = duration_cast<milliseconds>(end - start).count();
    cout << "Time taken to run the functions sequentially for " << n_iterations
         << " iterations: " << duration << " milliseconds." << endl;
}

int main() {
    // Define the flag sequence
    int flag[] = {0, 1, 1, 1, 1, 1, 1, 0}; // 01111110
    int flagSize = sizeof(flag) / sizeof(flag[0]);
    cout << "Flag:";
    for (int i = 0; i < flagSize; i++) {
        cout << flag[i];
    }
    cout << endl;

    // Define the original data
    int data[] = {1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0};
    int dataSize = sizeof(data) / sizeof(data[0]);
    cout << "Original Data:";
    for (int i = 0; i < dataSize; i++) {
        cout << data[i];
    }
    cout << endl;

    // Step 1: Apply bit stuffing on the data
    int stuffedSize;
    int* stuffedData = bitStuffing(data, dataSize, stuffedSize);
    cout << "After Bit Stuffing:";
    for (int i = 0; i < stuffedSize; i++) {
        cout << stuffedData[i];
    }
    cout << endl;

    // Step 2: Add flags to the stuffed data
    int framedSize;
    int* framedData = addFlags(stuffedData, stuffedSize, flag, flagSize, framedSize);
    delete[] stuffedData;
    cout << "After Adding Flags: ";
    for (int i = 0; i < framedSize; i++) {
        cout << framedData[i];
    }
    cout << endl;

    // Step 3: Remove flags from the framed data
    int unframedSize;
    int* unframedData = removeFlags(framedData, framedSize, flag, flagSize, unframedSize);
    delete[] framedData;
    cout << "After Removing Flags: ";
    for (int i = 0; i < unframedSize; i++) {
        cout << unframedData[i];
    }
    cout << endl;

    // Step 4: Apply bit destuffing to get the original data back
    int destuffedSize;
    int* destuffedData = bitDestuffing(unframedData, unframedSize, destuffedSize);
    delete[] unframedData;
    cout << "After Bit Destuffing: ";
    for (int i = 0; i < destuffedSize; i++) {
        cout << destuffedData[i];
    }
    cout << endl;

    delete[] destuffedData;

    // Measure the time taken to run the functions
    cout << "Measuring time taken to run the functions..." << endl;

    // Number of iterations to run the functions
    int n_iterations = 1000;
    dataSize = 12000;

    // Measure the time taken to run the functions
    measure_time(n_iterations, flag, flagSize, dataSize);

    return 0;
}
