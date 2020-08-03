import os
import subprocess 

last = 0
def new_name(s):
    global last 
    last += 1
    return s + str(last)

long = ""
with open("scratch.sml", 'r') as f:
    text = f.read()
    lines = len(text.splitlines())
    total = 0

    while total < 10000:
        s = text
        s = s.replace('merge', new_name('merge'))
        s = s.replace('type_check', new_name('type_check'))
        long += s 
        total += lines

open('long.sml', 'w').write(long)
subprocess.run(["cargo", "build", "--release"])
bench = subprocess.run(["target/release/sml-driver.exe", "--measure", "long.sml"], capture_output=True)
print(bench.stdout.decode("utf-8"))
os.remove('long.sml')