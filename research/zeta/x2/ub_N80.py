from circle_dnn_ub import dnn_b
from circle_dnn_lb import dnn_lb
from circle_dnn_gap import dnn_gap
N=80; M=12*N
print('N=80 none', round(dnn_b(N,M,lambda a:0,lambda a:None),4), flush=True)
print('S<=2 on (1,1.05]', round(dnn_b(N,M,lambda a:0,lambda a:2 if a<=1.05 else None),4), flush=True)
print('S<=1 on (1,1.25]', round(dnn_b(N,M,lambda a:0,lambda a:1 if a<=1.25 else None),4), flush=True)
print('GGOS lower', round(2-dnn_lb(N,M,lambda a:max(1.5-a,0),1.5),4), flush=True)
print('distinct gaps<0.5 >=0.05', round(dnn_gap(N,M,0.5,0.05),4), flush=True)
