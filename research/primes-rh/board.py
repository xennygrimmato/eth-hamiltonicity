#!/usr/bin/env python3
"""Shared board. Usage:
 board.py read                      # announcements, open subtasks, last 30 notes, landed
 board.py note AGENT "msg"
 board.py add AGENT "title" "detail"
 board.py claim AGENT ID            # atomic; prints OK or TAKEN
 board.py done AGENT ID
 board.py land AGENT "what" "file" "[R]|[N]|[C]"
"""
import sqlite3,sys,os
c=sqlite3.connect(os.path.join(os.path.dirname(os.path.abspath(__file__)),'board.db'),timeout=30)
a=sys.argv[1:]
if not a or a[0]=='read':
    for t,q in [('ANNOUNCE','select id,ts,msg from announce order by id'),('SUBTASKS','select id,status,owner,creator,title,detail from subtasks order by id'),('NOTES (last 30)','select * from (select id,ts,agent,msg from notes order by id desc limit 30) order by id'),('LANDED','select id,ts,agent,status,what,file from landed order by id')]:
        print('==',t)
        for r in c.execute(q): print(' | '.join(str(x) for x in r))
elif a[0]=='note': c.execute('insert into notes(agent,msg) values(?,?)',(a[1],a[2]))
elif a[0]=='add': c.execute('insert into subtasks(creator,title,detail) values(?,?,?)',(a[1],a[2],a[3] if len(a)>3 else '')); print(c.execute('select last_insert_rowid()').fetchone()[0])
elif a[0]=='claim':
    n=c.execute("update subtasks set owner=?,status='claimed' where id=? and owner is null",(a[1],int(a[2]))).rowcount; print('OK' if n else 'TAKEN')
elif a[0]=='done': c.execute("update subtasks set status='done' where id=? and owner=?",(int(a[2]),a[1]))
elif a[0]=='land': c.execute('insert into landed(agent,what,file,status) values(?,?,?,?)',(a[1],a[2],a[3],a[4]))
elif a[0]=='announce': c.execute('insert into announce(msg) values(?)',(a[1],))
c.commit()
