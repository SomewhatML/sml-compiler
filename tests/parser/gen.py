
long = ""
with open("decls.sml", 'r') as f:
    text = f.read()
    lines = len(text.splitlines())
    total = 0
    while total < 10000:
        long += text 
        total += lines

open('long.sml', 'w').write(long)