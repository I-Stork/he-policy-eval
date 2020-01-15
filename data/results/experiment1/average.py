#!/usr/bin/env python3

graph = ""
with open("results.txt") as fh:
    outputs = fh.readlines()
    cur_time = 0
    cur_bandwidth = 0

    for output in outputs:
        line = output.split("===")
        data = line[0].split(",")
        targets = int(data[0][1:])
        #operations = int(data[1])
        query_size = int(data[2])
        smoothness = int(data[3][:-1])
        time = float(line[2][1:-1])
        bandwidth = int(line[3][1:-2])

        cur_time += time
        cur_bandwidth += bandwidth

        if smoothness == 50:
            avg_time = round(cur_time / 50, 6)
            avg_bandwidth = round(cur_bandwidth / 50)
            graph += "%d, %f, %d\n" % (query_size, avg_time, avg_bandwidth)

            cur_time = 0
            cur_bandwidth = 0

print(graph[:-1])
