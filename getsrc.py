# Gets all the source files for `llvm-idr.ipkg`
import glob

files0 = glob.glob('./src/**/*.idr', recursive=True)
files1 = [file[6:-4] for file in files0]
files2 = [file.replace('/','.') for file in files1]
print("\n\n========Source Files========\n\n")
for file in files2:
    print(file + ",")
