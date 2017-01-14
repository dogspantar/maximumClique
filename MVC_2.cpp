#include<stdio.h>
#include<stdlib.h>
#include<fstream>
#include<iostream>
#include<math.h>
#include<time.h>
#include<vector>
#include<array> 

using namespace std;

#define N 200 // 网络节点数 
#define Tmax 10 // 最大迭代次数 
#define Pmax 0.99 // 概率终止条件 
#define a 0.4
#define b 0
#define RunTime 3// 统计RunTime次的运行结果，求平均

//********************************************  变量定义  *******************************************
array< array<int, N>, N > matrix; // 网络的邻接矩阵 
array< array<int, N>, N > matrix_temp; // 用于求网络的补图
vector< vector<int> > adjList; //网络邻接表，存储节点的邻居节点的标号 
vector<int> adjList_line;
int deg[N]; // 网络中每个节点的度
int maxdegree; // 最大度 
int mindegree; // 最小度 
double avedegree; // 平均度 
int edgenumber; // 网络总边数 

array< int, N > cover; // 解集
array< int, N > state; // 每个节点的状态，state=1，表示已经被激活过；state=2, 表示正在被激活； state=3，表示从没有被激活过 
array< int, N > actIndex; // 如果自动机被激活，则记录被激活后选择的行为在其行为集中的排号 
 
vector< vector<double> > proVector; // 每个节点的行为概率向量  
vector<double> proVector_line;
vector< vector<double> > proVector_temp; // 保存概率向量，即使自动机的某个行为被删除，可是当下一次重新选择时
										 // 每个自动机的行为集合都回复，此时仍然需要每一个自动机的完整的行为概率 
vector< double > proVector_temp_line;
vector< vector<int> > action; // 每个节点的行为概率向量 
vector<int> action_line;

array< int, Tmax > dynamicThreshold; // 动态阈值
array< double, Tmax > probabilityProduct;

array< array<int, N>, RunTime > solution; // RunTime次运行，每一次得到的解集
int solutionCardinality[RunTime]; // RunTime次运行，每一次得到的解集的元素个数，即得到的独立集的元素个数
int totalIterationTimes[RunTime];
double solutionRunningTime[RunTime]; // RunTime次运行，每一次的运行时间
double averageCardinality;// RunTime次运行，独立集大小的平均值 
double stdCardinality;// RunTime次运行，独立集大小的标准差
int maxCardinality;// RunTime次运行中candidate的最大值 
int minCardinality;// RunTime次运行中candidate的最小值 
int maxCardinalityNumber;// RunTime次运行中得到最大candidate的次数
int minCardinalityNumber;// RunTime次运行中得到最大candidate的次数
double averageRunningTime;// RunTime次运行的平均运行时间
double averageIterationTimes; // RunTime次运行的平均迭代次数 

double runningTime; // 每一次运行的运行时间 
int run_times; // 记录运行次数 run_times = run+1 

int coverSize[Tmax]; // 每一次迭代得到的覆盖集的大小，每一次独立运行前，将这个变量进行初始化 

vector<double> recordProbability;
 
//********************************************  函数声明  **********************************************
void read();
void read_without_e();
void readMatrix();
void complement_graph();
void initialVariables();
void initialVariablesRunTime();
void obtainAdjList();
void obtainVerDegree();
void initialIteration();
void initialVariables_while();
int chooseVertexRandomly();
int chooseAction( int vx );
int moveOrNot( int vy );
int vertexCoverOrNot( int vx );
void updateActionSet( int vx );
int checkActionSize( int vx );
void computeDynamicThreshold( int it );
void rewardProbabilityVertor();
void penalityProbabilityVector();
double computeProProduct();
int computeCoverSize();
int findMaxCardinality();
int findMaxCardinalityNumber();
int findMinCardinality();
int findMinCardinalityNumber();
double computeAverageCardinality();
double computeStdCardinality();
void saveResults();
void printResults();
double computeAverageRunningTime();
double computeAverageIterationTimes();


//********************************************  main  *******************************************
int main()
{
	int i;
	int j;
	int run;
	int iter;
	clock_t start;
	clock_t end;
	srand( (unsigned)time(NULL) );
	
	initialVariables(); //初始化变量
	
	read();
	complement_graph();
	//read_without_e(); 
	//readMatrix(); 
	
	obtainAdjList();
	obtainVerDegree();
	
	initialVariablesRunTime(); //初始化变量
	double proProduction;
	int vi = 0;
	int vj = 0;
	int indexMove = 0;
	int actionSizeZeroOrNot = 0;
	for( run=0; run<RunTime; run++ ) // 进行RunTime次独立实验 
	{
		initialIteration(); //初始化每个节点都在解集中，初始化每个节点的行为概率向量 
		
		iter = 0; //迭代次数指示器 
		proProduction = 0.5; // 解集中的节点的概率乘积 
		 
		start = clock();
		while( iter<Tmax && proProduction<Pmax ) //当不满足终止条件时，则一直迭代
		{
			initialVariables_while(); 
			
			vi = chooseVertexRandomly(); // 随机选择一个节点 
			cover[vi] = 0; // 将vi从覆盖集中移出
			state[vi] = 1; // 节点vi被选中过，则不能再次被激活 
			updateActionSet( vi );
			
			int actionSize = 1; // 正在被激活的节点的可选的行为的数目 
			while( actionSize>0 )
			{
				vj = chooseAction( vi ); // 节点vi对应的自动机选择一个行为 
				state[vj] = 1;
				updateActionSet( vj ); // 更新vj的邻居的行为集合和对应的行为概率 
				
				// 记录每一个被激活的节点所选择的行为的标号 
				indexMove = vertexCoverOrNot( vj );
				if( indexMove==1 ) // 如果将vj移走后，依旧是覆盖集，则将vj从cover中移走
				{
					cover[vj] = 0; 
				} 
				else
				{
					cover[vj] = 1; // 否则，vj仍旧在覆盖集中 
				}
				vi = vj; //将vj赋给vi，重新迭代
				actionSizeZeroOrNot = checkActionSize( vi ); // 如果这个节点的行为数目为0了，则该自动机没办法再选择行为，则一轮迭代结束 
			    if( actionSizeZeroOrNot==0 ) // 可选的行为数目不为0
				{
					actionSize = 1; 
				} 
				else if( actionSizeZeroOrNot==1 )
				{
					actionSize = 0;
				}
			} 
			coverSize[iter] = computeCoverSize();
			computeDynamicThreshold( iter+1 ); //计算迭代了iter次时的动态阈值，用于奖励或者惩罚 
			if( coverSize[iter]<=dynamicThreshold[iter] )
			{
				rewardProbabilityVertor();
			} 
			else
			{
				penalityProbabilityVector();
			}
			
			/*for( i=0; i<recordProbability.size(); i++ )
			{
				printf("%f ",recordProbability[i]);
			}
			printf("\n");*/
			proProduction = computeProProduct();	
			//printf("proProduction = %f \n",proProduction);
			iter = iter+1;		
		} 
		end = clock();
		printf("proProduction = %f \n",proProduction);
		runningTime = (double) (end-start)/CLOCKS_PER_SEC;
		solutionRunningTime[run] = runningTime; //每一次运行的运行时间 
		totalIterationTimes[run] = iter; // 每次运行，总迭代次数 
		solution[run] = cover; // 每次运行，得到的解集
		solutionCardinality[run] = computeCoverSize(); 
	}
	
	// RunTime次运行的实验结果求平均 
	maxCardinality = findMaxCardinality(); // 找到最大值 
	maxCardinalityNumber = findMaxCardinalityNumber(); // 最大值出现的次数 
	minCardinality = findMinCardinality(); // 找到最小值 
	minCardinalityNumber = findMinCardinalityNumber(); // 最小值出现的次数 
	averageCardinality = computeAverageCardinality(); // 计算平均值 
	stdCardinality = computeStdCardinality(); //计算标准差 
	averageRunningTime = computeAverageRunningTime(); // 计算平均运行时间 
	averageIterationTimes = computeAverageIterationTimes(); // 计算平均迭代次数 

	//输出并保存实验结果 
	printResults();
	saveResults();
	
	return 0;
}

//***************  1  读取文件（网络的边的表示）  **************************
void read() // 得到了网络邻接矩阵 ， 并记录了边的矩阵edgeMatrix[M][2] 
{
	int i;
	//int j;
	
	//FILE* fp = fopen("vertex6.txt","r");
	FILE* fp = fopen("brock200_2 (12).txt","r");
	//FILE* fp = fopen("frb30-15-1_450_17827.txt","r");
	
	if( !fp )
	{
		printf("文件打开错误");
	}

	char e;
	int startnode;
	int endnode;
	
	i=0;
	while( !feof(fp) )
	{
		fscanf(fp, "%c %d %d \n", &e, &startnode, &endnode );
		matrix[startnode-1][endnode-1] = 1;
		matrix[endnode-1][startnode-1] = 1;
		i = i+1;
	}

	fclose( fp );
}

//***************  1  读取文件（网络的边的表示）  **************************
void read_without_e() // 得到了网络邻接矩阵 ， 并记录了边的矩阵edgeMatrix[M][2] 
{
	int i;
	//int j;
	
	FILE* fp = fopen("2000 25 70 （1）.txt","r");
	
	if( !fp )
	{
		printf("文件打开错误");
	}

	int startnode;
	int endnode;
	
	i=0;
	while( !feof(fp) )
	{
		fscanf(fp, "%d %d \n", &startnode, &endnode );
		matrix[startnode-1][endnode-1] = 1;
		matrix[endnode-1][startnode-1] = 1;
		i = i+1;
	}

	fclose( fp );
}

//***************  2  读取邻接矩阵表示的网络  **************************
void readMatrix()
{
	//int i;
	//int j;
	
	FILE* fp;
	
	fp = fopen( "ws2000（p=0.1）.txt" , "r" );
	
	if ( fp==NULL )
	{
		printf("文件打开失败");
		exit( 1 );
	}
	char C;
	int row=0;
	int col=0;
	int i1 = 0;//由于matrix的下标需要每次递增1，所以这里另外设置两个迭代器i1和j1
	int j1 = 0;
	while( ( C=fgetc(fp) ) != EOF )
	{
		if ( C=='0' )
		{
			matrix[i1][j1]=0;
			col++;
			j1++;
		}
		else if ( C=='1' )
		{
			matrix[i1][j1]=1;
			col++;
			j1++;
		}
		else if ( C== ' ' )
		{
			col++;
		}
		else if( C == '\n')
		{
			col++;
			row++;
			i1++;
			j1 = 0;
		}
	}
	fclose(fp);
}

//***************************  5  求网络的补图  *****************************
void complement_graph()
{
	int i;
	int j;	
	for( i=0; i<N; i++ )
	{
		for( j=0; j<N; j++ )
		{
			matrix_temp[i][j] = matrix[i][j];
		}
	}	
	for( i=0; i<N; i++ )
	{
		for( j=0; j<N; j++ )
		{
			if( matrix_temp[i][j]==1 )
			{
				matrix[i][j] = 0;
			}
			else if( matrix_temp[i][j]==0 )
			{
				matrix[i][j] = 1;
			}
		}
	}	
	for( i=0; i<N; i++ )
	{
		matrix[i][i] = 0; 
	}
}

//***********************************************
void initialVariables() //初始化变量
{
	int i;
	int j;
	
	for( i=0; i<N; i++ )
	{
		for( j=0; j<N; j++ )
		{
			matrix[i][j] = 0;
			matrix_temp[i][j] = 0;
		}
	}
	
	for( i=0; i<N; i++ )
	{
		adjList.push_back( adjList_line );
		proVector.push_back( proVector_line );
		proVector_temp.push_back( proVector_temp_line );
		action.push_back( action_line );
	}
	
	for( i=0; i<N; i++ )
	{
		deg[i] = 0;
	}
	
	maxdegree = 0;
	mindegree = 0;
	avedegree = 0;
	edgenumber = 0;
} 

//***********************************************
void initialVariablesRunTime() //初始化变量
{
	int i;
	int j;
	for( i=0; i<RunTime; i++ )
	{
		for( j=0; j<N; j++ )
		{
			solution[i][j] = 0;
		}
	}
	for( i=0; i<RunTime; i++ )
	{
		solutionCardinality[i] = 0;
		totalIterationTimes[i] = 0;
		solutionRunningTime[i] = 0;
	}
	averageCardinality = 0;
	stdCardinality = 0;
	maxCardinality = 0;
	minCardinality = 0;
	maxCardinalityNumber = 0;
	averageRunningTime = 0;
	
}

//************************************  6  得到网络邻接表  ************************************
void obtainAdjList()
{
	int i;
	int j;
	
	for( i=0; i<N; i++ )
	{
		adjList[i].clear();
	}
	for( i=0; i<N; i++ )
	{
		for( j=0; j<N; j++ )
		{
			if( matrix[i][j]==1 )
			{
				adjList[i].push_back(j); //  得到的邻接表中，每一个节点的邻居节点都以标号的升序排列 
			}
		}
	}
}

//********************************  7  得到网络的度信息  *****************************
void obtainVerDegree()
{
	int i;

	for( i=0; i<N; i++ )
	{
		deg[i] = adjList[i].size();
	}
	
	int max = deg[0];
	for( i=0; i<N; i++ )
	{
		if( max<deg[i] )
		{
			max = deg[i];
		}
	} 
	maxdegree = max; // 最大度 
	
	int min = deg[0];
	for( i=0; i<N; i++ )
	{
		if( min>deg[i] )
		{
			min = deg[i];
		}
	}
	mindegree = min; // 最小度  
	
	double sumdegree = 0;
	for( i=0; i<N; i++ )
	{
		sumdegree = sumdegree + deg[i];
	}
	avedegree = (double)( (double)sumdegree/ (double)N); // 平均度 
	
	edgenumber = (int)( sumdegree/ 2); // 总边数 
}

//********************************  每次运行前的初始化  ******** 
void initialIteration()
{
	int i;
	int j;
	for( i=0; i<N; i++ )
	{
		cover[i] = 1;
		state[i] = 3; //初始时，所有节点都处于未激活状态，都可以被激活 
		actIndex[i] = N; // 初始时，所有节点的选择的行为都设为标号N 
		proVector[i].clear();
		proVector_temp.clear();
	}
	for( i=0; i<N; i++ )
	{
		for( j=0; j<deg[i]; j++ )
		{
			proVector[i].push_back( (double)( (double)1 / (double)(deg[i]) ) ); 
			proVector_temp[i].push_back( (double)( (double)1 / (double)(deg[i]) ) ); 
		} 
	}
	for( i=0; i<Tmax; i++ )
	{
		coverSize[i] = 0;
	} 
}

//********************************
void initialVariables_while() 
{
	int i;
	int j;
	for( i=0; i<N; i++ )
	{
		cover[i] = 1;
		state[i] = 3;
		actIndex[i] = N;
	}
	for( i=0; i<N; i++ )
	{
		action[i].clear();
		proVector[i].clear();
	} 
	for( i=0; i<N; i++ )
	{
		for( j=0; j<adjList[i].size(); j++ )
		{
			action[i].push_back( adjList[i][j] );
		}
	}
	
	for( i=0; i<N; i++ )
	{
		for( j=0; j<proVector_temp[i].size(); j++ )
		{
			proVector[i].push_back( proVector_temp[i][j] );
		} 
	}
	recordProbability.clear();
}

//********************************
int chooseVertexRandomly() // 从N个节点中随机选择一个初始节点 
{
	//int i;
	//int j;
	
	int chosenIndex;
	chosenIndex = (int)(N * rand()) / (RAND_MAX+1);
	return chosenIndex;
} 

//********************************
int chooseAction( int vx ) // 被激活的节点从自己的行为集合中，根据行为概率选择一个行为 
{
	int i;
	int j;
	int chosenVertex;
	double maxPro;
	int maxIndex;
	maxPro = proVector[vx][0];
	maxIndex = 0;
	for( i=0; i<proVector[vx].size(); i++ )
	{
		if( maxPro<proVector[vx][i] )
		{
			maxPro = proVector[vx][i];
			maxIndex = i;
		}
	}
	chosenVertex = action[vx][maxIndex];
	actIndex[vx] = maxIndex; // 记录节点vx选择的行为的标号 
	recordProbability.push_back( maxPro );
	return chosenVertex;
} 

//********************************
int moveOrNot( int vy ) // 将节点vj从行为覆盖集中移出后，判断是否还是覆盖集 
{
	int i;
	int j;
	int index; // index=1,表示移出后仍然是覆盖集，vj可以移出；否则，index=0, vj不可以移出
	//cover[vy] = 0; //vj移出前是覆盖集，所以只需要判断与vj相连的边，在vj移出后，是否仍被覆盖 
	index = vertexCoverOrNot( vy ); 
	return index;
} 

//********************************
int vertexCoverOrNot( int vx )
{
	int i;
	int j;
	int idx;
	int s = 0;
	for( i=0; i<adjList[vx].size(); i++ )
	{
		if( cover[adjList[vx][i]]==0 )
		{
			s = s+1;
		}
	}
	if( s>0 )
	{
		idx = 0; // 所有的邻居中，只有有至少一个邻居不在覆盖集中，则与这个邻居之间的边就不能被覆盖，
				 // 则这个节点不能移出 
	    //cover[vx] = 1;
	}
	else
	{
		idx = 1; // 节点可以移出 
	}
	/*for( i=0; i<adjList[vx].size(); i++ )
	{
		if( cover[adjList[vx][i]]==1 )
		{
			s = s+1;
		}
	}
	if( s==adjList[vx].size() )
	{
		idx = 1; // vx的所有邻居节点都在cover中，所以vx的移出，不会影响vx的边的覆盖状态 
	}
	else
	{
		idx = 0;
	}*/
	return idx;
}

//********************************
void updateActionSet( int vx ) // 更新与vi相连的未被激活的自动机的行为集合
{
	// vx移出后，将vx从其他自动机的行为集合中移出
	// 从vx的邻居的邻居中，删除vx 
	int i;
	int j;
	int k;
	int z;
	int t;
	int vxNeighbor;
	int vxPosition;
	vector<int> action_temp;
	vector<double> actionPro_temp; 
	action_temp.clear();
	actionPro_temp.clear();
	//printf("%d ",vx);
	for( i=0; i<adjList[vx].size(); i++ )
	{
		action_temp.clear();
		actionPro_temp.clear();
		
		vxNeighbor = adjList[vx][i];
		//if( state[vxNeighbor]==3 )// 第三种状态，还没有被激活过
		//{
			//从vxNeighbor的行为集中，把vx删除 
			for( j=0; j<action[vxNeighbor].size(); j++ )
			{
				//printf("%d ",action[vxNeighbor][j]);
				
				if( action[vxNeighbor][j]!=vx )
				{
					action_temp.push_back( action[vxNeighbor][j] );
					actionPro_temp.push_back( proVector[vxNeighbor][j] ); 
				}
				else
				{
					vxPosition = j; // vx在其邻居的行为集中的位置 
				}
			}
			/*for( i=0; i<action_temp.size(); i++ )
			{
				printf("%d, %f ",action_temp[i], actionPro_temp[i]);
			}
			printf("\n");*/
			action[vxNeighbor].clear();
			proVector[vxNeighbor].clear();
			for( k=0; k<action_temp.size(); k++ )
			{
				action[vxNeighbor].push_back( action_temp[k] );
				proVector[vxNeighbor].push_back( actionPro_temp[k] );
			}
			
			//更新行为概率向量
			double proSum = 0;
			for( z=0; z<proVector[vxNeighbor].size(); z++ )
			{
				proSum = proSum+proVector[vxNeighbor][z];
			} 
			for( t=0; t<proVector[vxNeighbor].size(); t++ )
			{
				proVector[vxNeighbor][t] = proVector[vxNeighbor][t] / proSum;
			}
		//} 
	}	 
}

//********************************
int checkActionSize( int vx ) // 判断vx的可选的行为的数目是否为0，如果为0，则这个节点不可以再次选择行为 
{
	int i;
	//int j;
	int actionIndex = 3;
	//int vxActionSize;
	int fail = 0;
	for( i=0; i<adjList[vx].size(); i++ )
	{
		if( state[adjList[vx][i]]==1 )
		{
			fail = fail+1;
		}
	}
	if( fail==adjList[vx].size() ) // 节点vx的所有邻居节点都已经被激活过，则节点vx没有可选行为了 
	{
		actionIndex = 1;
	}
	else 
	{
		actionIndex = 0;
	} 
	/*if( action[vx].size()==0 )
	{
		vxActionSize = 0;
		actionIndex = 0;
	}
	else
	{
		actionIndex = 1;
	}*/
	return actionIndex;
}

//********************************
void computeDynamicThreshold( int it ) // 迭代到第it次时，0-it次迭代的平均cover大小
{
	int i;
	int j;
	//int k;
	int aveCoverSize;
	int sumCoverSize = 0; 
	for( i=0; i<it; i++ )
	{
		sumCoverSize = sumCoverSize+coverSize[i];
	}
	aveCoverSize = (int)( sumCoverSize / it );
	dynamicThreshold[it-1] = aveCoverSize;
} 

//********************************
void rewardProbabilityVertor() // 奖励在这一轮中，所有被激活的节点的行为概率 
{
	int i;
	int j;
	int activatedVer;
	for( i=0; i<N; i++ )
	{
		if( state[i]==1 ) // 第二种状态，被激活过 
		{
			activatedVer = i;
			for( j=0; j<action[activatedVer].size(); j++ )
			{
				//找到这一轮迭代中，activatedVer所选的行为在其行为里的排号actIndex
				if( j==actIndex[i] )
				{
					//proVector[activatedVer][j] = proVector[activatedVer][j] + a*(1-proVector[activatedVer][j]);
					proVector_temp[activatedVer][j] = proVector_temp[activatedVer][j] + a*(1-proVector_temp[activatedVer][j]);
				} 
				else
				{
					//proVector[activatedVer][j] = (1-a)*proVector[activatedVer][j];
					proVector_temp[activatedVer][j] = (1-a)*proVector_temp[activatedVer][j];
				}
			} 
		}
	} 
}


//********************************
void penalityProbabilityVector()
{
	int i;
	int j;
	int activatedVer;
	for( i=0; i<N; i++ )
	{
		if( state[i]==1 ) // 第二种状态，被激活过，被激活过的自动机选择的是什么行为也需要记录 
		{
			activatedVer = i;
			for( j=0; j<action[activatedVer].size(); j++ )
			{
				//找到这一轮迭代中，activatedVer所选的行为在其行为里的排号actIndex
				if( j==actIndex[i] )
				{
					//proVector[activatedVer][j] = 1 - b*proVector[activatedVer][j];
					proVector_temp[activatedVer][j] = 1 - b*proVector_temp[activatedVer][j];
				} 
				else
				{
					//proVector[activatedVer][j] =( b / (action[activatedVer].size()-1) ) + (1-b)*proVector[activatedVer][j];
					proVector_temp[activatedVer][j] =( b / (action[activatedVer].size()-1) ) + (1-b)*proVector_temp[activatedVer][j];
				} 
			} 
		}
	} 
}


//********************************
double computeProProduct() // 计算当前的最大概率
{
	int i;
	double multiP = 1;
	for( i=0; i<recordProbability.size(); i++ )
	{
		multiP = multiP*recordProbability[i];
	}
	printf("recordProbability.size() = %d\n",recordProbability.size());
	/*printf("recordProbability:\n");
	for( i=0; i<recordProbability.size(); i++ )
	{
		printf("%f ",recordProbability[i]);
	}
	printf("\n");*/
	/*int j;
	int k;
	int z;
	double multiP = 1;
	int coverVertex;
	int coverVertexNeibor;
	double coverVertexMaxPro;
	vector<double> pro;
	vector<double> maxPro;
	for( i=0; i<N; i++ )
	{
		if( cover[i]==1 )
		{
			coverVertex = i; 
			pro.clear();
			for( j=0; j<adjList[coverVertex].size(); j++ )
			{
				coverVertexNeibor = adjList[coverVertex][j];
				//找到coverVertex的邻居选择coverVertex的概率 
				for( k=0; k<action[coverVertexNeibor].size(); k++ )
				{
					if( coverVertex == action[coverVertexNeibor][k] )
					{
						pro.push_back( proVector[coverVertexNeibor][k] );
					}
				}
			}
			coverVertexMaxPro = pro[0];
			for( z=0; z<pro.size(); z++ )
			{
				if( coverVertexMaxPro<pro[z] )
				{
					coverVertexMaxPro = pro[z];
				}
			}
			maxPro.push_back( coverVertexMaxPro );
		}
	}
	for( i=0; i<maxPro.size(); i++ )
	{
		multiP = multiP*maxPro[i];
	} */
	return multiP;
} 

//********************************
int computeCoverSize() // 计算cover中1的个数
{
	int i;
	//int j;
	int cs = 0;
	for( i=0; i<N; i++ )
	{
		if( cover[i]==1 )
		{
			cs = cs+1;
		}
	}
	return cs;
} 

//********************************
int findMaxCardinality()
{
	int i;
	//int j;
	int max = solutionCardinality[0];
	for( i=0; i<RunTime; i++ )
	{
		if( max<solutionCardinality[i] )
		{
			max = solutionCardinality[i];
		}
	}
	return max;
}


//********************************
int findMaxCardinalityNumber()
{
	int i;
	int maxNum = 0;
	for( i=0; i<RunTime; i++ )
	{
		if( solutionCardinality[i]==maxCardinality )
		{
			maxNum = maxNum+1;
		}
	}
	return maxNum;
}

//********************************
int findMinCardinality()
{
	int i;
	//int j;
	int min = solutionCardinality[0];
	for( i=0; i<RunTime; i++ )
	{
		if( min>solutionCardinality[i] )
		{
			min = solutionCardinality[i];
		}
	}
	return min;
}

//********************************
int findMinCardinalityNumber()
{
	int i;
	int minNum = 0;
	for( i=0; i<RunTime; i++ )
	{
		if( solutionCardinality[i]==minCardinality )
		{
			minNum = minNum+1;
		}
	}
	return minNum;
}




//********************************
double computeAverageCardinality()
{
	int i;
	//int j;
	double sumCardinality = 0;
	double ave;
	for( i=0; i<RunTime; i++ )
	{
		sumCardinality = sumCardinality+solutionCardinality[i];
	}
	ave = (double)( (double)sumCardinality / (double)RunTime );
	return ave;
}


//********************************
double computeStdCardinality()
{
	int i;
	//int j;
	double s = 0;
	double std;
	for( i=0; i<RunTime; i++ )
	{
		s = s+( averageCardinality-solutionCardinality[i] )*( averageCardinality-solutionCardinality[i] );
	}
	s = s / (double)RunTime;
	std = (double)( sqrt( s ) );
	return std;
}

//********************************
double computeAverageRunningTime()
{
	int i;
	//int j;
	double aveTime = 0;
	for( i=0; i<RunTime; i++ )
	{
		aveTime = aveTime+solutionRunningTime[i];
	}
	
	aveTime = (double)( aveTime / (double)RunTime );
	
	return aveTime;
}

//********************************
double computeAverageIterationTimes()
{
	int i;
	double aveIterationTimes = 0;
	for( i=0; i<RunTime; i++ )
	{
		aveIterationTimes = aveIterationTimes+totalIterationTimes[i];
	}
	aveIterationTimes = (double)( aveIterationTimes / (double)RunTime );
	return aveIterationTimes; 
}

//**********************************  26  将实验结果以文本格式进行存储  ************************************
void saveResults()
{
	int i;
	int j;
	
	ofstream outfile_tm("LA_MVC results.txt");
	if (!outfile_tm)
	{
		cerr << "open error!" << endl;
		exit(1);
	}
	outfile_tm << "The results:  "<<endl<<endl;
	
	outfile_tm << "Network vertices = " << N <<", ";
	outfile_tm << "the total run times = : "<< RunTime << endl;
	
	outfile_tm << "a = " << a <<", ";
	outfile_tm << "b = " << b <<", ";
	outfile_tm << "Tmax = " << Tmax <<", ";
	outfile_tm << "Pmax = " << Pmax << endl<< endl;
	
	outfile_tm << "total cardinality of RunTime: "<< " ";
	for( i=0; i<RunTime; i++ )
	{
		outfile_tm << solutionCardinality[i] << " ";
	}
	outfile_tm << endl;
	
	outfile_tm<<"averageCardinality: "<<averageCardinality<<endl<< endl;
	outfile_tm<<"stdCardinality: "<<stdCardinality<<endl<< endl;
	
	outfile_tm<<"minCardinality: "<<minCardinality<<endl<< endl;
	outfile_tm<<"minCardinalityNumber: "<<minCardinalityNumber<<endl<< endl;
	
	outfile_tm<<"maxCardinality: "<<maxCardinality<<endl<< endl;
	outfile_tm<<"maxCardinalityNumber: "<<maxCardinalityNumber<<endl<< endl;
	
	outfile_tm<<"averageRunningTime: "<<averageRunningTime<<endl<< endl;
	outfile_tm<<"averageIterationTimes: "<<averageIterationTimes<<endl<< endl;
	
	outfile_tm << "edge number =  : "<< edgenumber << endl<< endl;
	outfile_tm << "the maximum degree of the network is : "<< maxdegree << endl<< endl;
	outfile_tm << "the minimum degree of the network is : "<< mindegree << endl<< endl;
	outfile_tm << "the average degree of the network is : "<< avedegree << endl<< endl;

	outfile_tm << "the solution of RunTime: "<<endl;
	for( i=0; i<RunTime; i++ )
	{
		for( j=0; j<N; j++ )
		{
			if( solution[i][j]==1)
			{
				outfile_tm << j <<" ";
			}
		}
		outfile_tm << endl;
	}
	outfile_tm << endl;
}

//*******************************  27  结果输出  ***************************************** 
void printResults()
{
	int i;
	int j;
	
	
	printf("*********************  共运行 %d 次  *************************：\n\n",RunTime);
	
	printf("Network vertices = %d, run times = %d\n",N, RunTime);
	printf("a = %f, b = %f \n",a,b);
	printf("Tmax = %d, Pmax = %f \n\n",Tmax,Pmax);
	
	printf("1、得到的解集大小分别为： ");
	for( i=0; i<RunTime; i++ )
	{
		printf("%d ",solutionCardinality[i]);
	}
	printf("\n\n");
	
	printf("2、解集大小的平均值为：%f，标准差为：%f\n\n", averageCardinality, stdCardinality);
	
	printf("3、平均运行时间为：%f, 平均迭代次数为：%f \n\n", averageRunningTime, averageIterationTimes);
	
	printf("4、解集大小最小值为：%d, 取得最小值的次数为：%d\n\n", minCardinality, minCardinalityNumber);
	
	printf("5、解集大小最大值为：%d, 取得最大值的次数为：%d\n\n", maxCardinality, maxCardinalityNumber);
	
/*	printf("6、得到的解集中的元素分别为：\n");
	for( i=0; i<RunTime; i++ )
	{
		for( j=0; j<N; j++ )
		{
			if( solution[i][j]==1 )
			{
				printf("%d ",j);
			}			
		}
		printf("\n");
	}
	printf("\n");	*/
}












