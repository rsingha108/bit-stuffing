import exrex
import argparse

def valid_message_segment(b, k, s):
    if len(b) <= len(k):
        return True
    elif b.startswith(k):
        return b[len(k)] == s and valid_message_segment(b[len(k)+1:], k, s)
    else:
        return valid_message_segment(b[1:], k, s)

def valid_message_end(b, k, s):
    if len(b) < len(k):
        return True
    elif b.startswith(k):
        if len(b) == len(k):
            return False
        else:
            return b[len(k)] == s and valid_message_end(b[len(k)+1:], k, s)
    else:
        return valid_message_end(b[1:], k, s)

def no_flag_in_data(f, k, s):
    for i in range(len(k)+1):
        if valid_message_segment(k[0:i] + f, k, s):
            return False
    return True

def no_flag_overlapping_real_flag(f, k, s):
    for i in range(1,len(f)):
        if f[0:i] == f[-i:]:
            for j in range(len(k)+1):
                if valid_message_end(k[0:j] + f[0:-i], k, s):
                    # print(f"overlap probelem : f={f}, k={k}, i={i}, j={j}, [{k[0:j]}] + [{f[0:-i]}] = [{k[0:j] + f[0:-i]}]")
                    return False
    return True

def valid_protocol(f, k, s):
    return no_flag_in_data(f, k, s) and no_flag_overlapping_real_flag(f, k, s)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--flag", help="flag bits", required=True)
    parser.add_argument("-k", "--kernel", help="bit pattern after which to stuff", required=True)
    parser.add_argument("-s", "--stuff", help="stuffing bit", required=True)
    args = parser.parse_args()

    flags = list(exrex.generate(args.flag.replace(".", "[01]")))
    print("flags : ",flags)
    kernels = list(exrex.generate(args.kernel.replace(".", "[01]")))
    kr = args.kernel[:-1]
    while (kr != ""):
        kernels += list(exrex.generate(kr.replace(".", "[01]")))
        kr = kr[:-1]
    print("kernels : ",kernels)
    stuffs = list(exrex.generate(args.stuff.replace(".", "[01]")))

    count = 0
    workex = []
    for f in flags:
        for k in kernels:
            for s in stuffs:
                assert(0 < len(k) < len(f) and len(s) == 1)
                assert(all(c in "01" for c in f))
                assert(all(c in "01" for c in k))
                assert(all(c in "01" for c in s))

                if valid_protocol(f, k, s):
                    # print("Flag: " + f + " Kernel: " + k + " Stuff: " + s)
                    count += 1
                    workex = [[str(f).replace('1','T').replace('0','F'),str(k).replace('1','T').replace('0','F')]] + workex

    print("Total workex = ", count)
    # print(workex)
    ocaml_workex =  "(TTTFF, F) (TTTFF, TF) (TTTFF, TTF) (TTFTF, T) (TTFTF, FT) (TTFFT, F) (TTFFT, TF) (TTFFF, F) (TTFFF, TF) (TTFFF, FF) (TTFFF, TFF) (TFTFF, T) (TFTFF, F) (TFTFF, FT) (TFFTT, F) (TFFTF, F) (TFFFT, F) (TFFFT, FF) (TFFFF, F) (TFFFF, FF) (TFFFF, FFF) (FTTTF, T) (FTTTF, TTT) (FTTTF, FTTT) (FTTFT, TT) (FTTFT, FTT) (FTTFF, F) (FTTFF, TT) (FTTFF, TF) (FTTFF, FTT) (FTFTT, T) (FTFTT, FT) (FTFTF, T) (FTFTF, FT) (FTFFT, T) (FTFFT, F) (FTFFT, FT) (FTFFF, T) (FTFFF, F) (FTFFF, FT) (FTFFF, FF) (FFTTT, F) (FFTTF, F) (FFTTF, TT) (FFTTF, FTT) (FFTTF, FFTT) (FFTFT, T) (FFTFT, F) (FFTFT, FT) (FFTFT, FFT) (FFTFF, T) (FFTFF, F) (FFTFF, FT) (FFTFF, FFT) (FFFTT, F) (FFFTT, FF) (FFFTF, T) (FFFTF, F) (FFFTF, FT) (FFFTF, FF) (FFFTF, FFT) (FFFTF, FFFT) (FFFFT, F) (FFFFT, FF) (FFFFT, FFF) (FFFFF, F)"
    t1 = ocaml_workex.replace(') (',');(')
    t2 = t1.split(';')
    t3 = [t[1:-1].split(', ') for t in t2]
    # print("\nt3 : ",t3)
    # print("\n\nworkex : ",workex)

    for i in range(len(t3)):
        if t3[i] == workex[i]:
            print(f'#{i} : matching')
        else:
            print(f'#{i} : not matching : t3[{i}] = {t3[i]} ; workex[{i}] = {workex[i]}')





               
