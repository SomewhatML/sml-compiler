
long = ""
with open("decls.sml", 'r') as f:
    text = f.read()
    for i in range(0, 250):
        long += text 

open('long.sml', 'w').write(long)