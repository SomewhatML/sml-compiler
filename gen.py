

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
        text = text.replace('merge', new_name('merge'))
        text = text.replace('type_check', new_name('type_check'))
        long += text 
        total += lines

open('long.sml', 'w').write(long)