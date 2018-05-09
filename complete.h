
#ifndef COMPLETE_H
#define COMPLETE_H
#include <map>
	using namespace std;

class complete
{
private:
	struct inst
	{
		unsigned int ReadData, RegWrite, MemtoReg;
		unsigned int ALUOut, WriteReg;
	};
	inst i;
public:
	complete();
	void copy(vector <int> &com) {
		com.clear();
		for (map<int, inst >::const_iterator it = m.begin();
			it != m.end(); ++it)
		{
			com.push_back(it->first);
		}
	}
	int next(unsigned int &ReadDataWB, unsigned int &RegWriteWB, unsigned int &MemtoRegWB, unsigned int &ALUOutWB, unsigned int &WriteRegWB, int arr[50][2]);
	bool getnext();
	void insert(int n, unsigned int ReadDataC, unsigned int RegWriteC, unsigned int MemtoRegC, unsigned int ALUOutC, unsigned int WriteRegC, int arr[50][2]);
	void setNext(int i)
	{
		n = i;
	}
	map <int, inst> m;
	int n;
	bool isComp(int dst)
	{
		for (int i = 20; i >= 0; i--)
		{
			if (m.count(i))
				if (m[i].WriteReg == dst && m[i].RegWrite)
					return true;
		}
		return false;
	}
	int find(int dst)
	{
		for (int i = 20; i >= 0; i--)
		{
			if (m.count(i))
				if (m[i].WriteReg == dst && m[i].RegWrite)
					return (m[i].MemtoReg) ? m[i].ReadData : m[i].ALUOut;
		}
		return 0;
	}
	void print() {
		for (map<int, inst >::const_iterator it = m.begin();
			it != m.end(); ++it)
		{
			std::cout << dec << it->first << " ALUOUT: " << it->second.ALUOut << "  Regwrite: " << it->second.RegWrite << "\n";
		}
	}

};
complete::complete()
{
	n = 0;
	m.clear();
}
void complete::insert(int instNum, unsigned int ReadDataC, unsigned int RegWriteC, unsigned int MemtoRegC, unsigned int ALUOutC, unsigned int WriteRegC, int arr[50][2])
{
	inst i;
	i.ReadData = ReadDataC;
	i.RegWrite = RegWriteC;
	i.MemtoReg = MemtoRegC;
	i.ALUOut = ALUOutC;
	i.WriteReg = WriteRegC;
	if (m.count(instNum))
	{
		
		m[instNum] = i;

	}
	else
	{
		m.insert(pair<int, inst>(instNum, i));
	}

}
bool complete::getnext()
{
	return(m.count(n));
}
int complete::next(unsigned int &ReadDataWB, unsigned int &RegWriteWB, unsigned int &MemtoRegWB, unsigned int &ALUOutWB, unsigned int &WriteRegWB, int arr[50][2])
{
	inst i = m[n];
	ReadDataWB = i.ReadData;
	RegWriteWB = i.RegWrite;
	MemtoRegWB = i.MemtoReg;
	ALUOutWB = i.ALUOut;
	WriteRegWB = i.WriteReg;
	m.erase(n);
	int m = n;
	n++;
	while(arr[n][1] == -1)
	n++;
	return m;
}
#endif