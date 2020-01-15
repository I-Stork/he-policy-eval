all:
	g++ -g main.cpp parser.cpp policy.cpp djn.cpp powmod.cpp -L/usr/local/lib -I/usr/local/include -lgmp -O3 -o main

backup: backup.cpp
	g++ -g backup.cpp djn.cpp powmod.cpp -L/usr/local/lib -I/usr/local/include -lgmp -O3 -o backup
	./backup
