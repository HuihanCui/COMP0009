def compare_files(file1, file2):
    with open(file1, 'r', encoding='utf-8') as f1, open(file2, 'r', encoding='utf-8') as f2:
        line_num = 1
        while True:
            line1 = f1.readline()
            line2 = f2.readline()

            # Check if both lines are empty, which means end of both files
            if not line1 and not line2:
                break

            # Compare lines
            if line1 != line2:
                print(f"Difference at line {line_num}:")
                print(f"File 1: {line1.strip()}")
                print(f"File 2: {line2.strip()}")
                # print(line1[0], " line 2: ", line2[0])
                # for i in range(len(line1)):
                #     if line1[i] != line2[i]:
                #         print(line1[i], "\t", line2[i])
                print()

            line_num += 1

#compare_files('output.txt', 'output2.txt')
#compare_files('testinputs/testinputs/testinput1/output.txt', 'outputa.txt')
#compare_files('testinputs/testinputs/testinput2/output.txt', 'outputb.txt')
#compare_files('testinputs/testinputs/testinput3/output.txt', 'outputc.txt')
#compare_files('testinputs/testinputs/testinput4/output.txt', 'outputd.txt')
compare_files('testinputs/testinputs/testinput5/output.txt', 'outpute.txt')

