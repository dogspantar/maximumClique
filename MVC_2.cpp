#include<stdio.h>
#include<stdlib.h>
#include<fstream>
#include<iostream>
#include<math.h>
#include<time.h>
#include<vector>
#include<array> 

using namespace std;

#define N 200 // ����ڵ��� 
#define Tmax 10 // ���������� 
#define Pmax 0.99 // ������ֹ���� 
#define a 0.4
#define b 0
#define RunTime 3// ͳ��RunTime�ε����н������ƽ��

//********************************************  ��������  *******************************************
array< array<int, N>, N > matrix; // ������ڽӾ��� 
array< array<int, N>, N > matrix_temp; // ����������Ĳ�ͼ
vector< vector<int> > adjList; //�����ڽӱ��洢�ڵ���ھӽڵ�ı�� 
vector<int> adjList_line;
int deg[N]; // ������ÿ���ڵ�Ķ�
int maxdegree; // ���� 
int mindegree; // ��С�� 
double avedegree; // ƽ���� 
int edgenumber; // �����ܱ��� 

array< int, N > cover; // �⼯
array< int, N > state; // ÿ���ڵ��״̬��state=1����ʾ�Ѿ����������state=2, ��ʾ���ڱ���� state=3����ʾ��û�б������ 
array< int, N > actIndex; // ����Զ�����������¼�������ѡ�����Ϊ������Ϊ���е��ź� 
 
vector< vector<double> > proVector; // ÿ���ڵ����Ϊ��������  
vector<double> proVector_line;
vector< vector<double> > proVector_temp; // ���������������ʹ�Զ�����ĳ����Ϊ��ɾ�������ǵ���һ������ѡ��ʱ
										 // ÿ���Զ�������Ϊ���϶��ظ�����ʱ��Ȼ��Ҫÿһ���Զ�������������Ϊ���� 
vector< double > proVector_temp_line;
vector< vector<int> > action; // ÿ���ڵ����Ϊ�������� 
vector<int> action_line;

array< int, Tmax > dynamicThreshold; // ��̬��ֵ
array< double, Tmax > probabilityProduct;

array< array<int, N>, RunTime > solution; // RunTime�����У�ÿһ�εõ��Ľ⼯
int solutionCardinality[RunTime]; // RunTime�����У�ÿһ�εõ��Ľ⼯��Ԫ�ظ��������õ��Ķ�������Ԫ�ظ���
int totalIterationTimes[RunTime];
double solutionRunningTime[RunTime]; // RunTime�����У�ÿһ�ε�����ʱ��
double averageCardinality;// RunTime�����У���������С��ƽ��ֵ 
double stdCardinality;// RunTime�����У���������С�ı�׼��
int maxCardinality;// RunTime��������candidate�����ֵ 
int minCardinality;// RunTime��������candidate����Сֵ 
int maxCardinalityNumber;// RunTime�������еõ����candidate�Ĵ���
int minCardinalityNumber;// RunTime�������еõ����candidate�Ĵ���
double averageRunningTime;// RunTime�����е�ƽ������ʱ��
double averageIterationTimes; // RunTime�����е�ƽ���������� 

double runningTime; // ÿһ�����е�����ʱ�� 
int run_times; // ��¼���д��� run_times = run+1 

int coverSize[Tmax]; // ÿһ�ε����õ��ĸ��Ǽ��Ĵ�С��ÿһ�ζ�������ǰ��������������г�ʼ�� 

vector<double> recordProbability;
 
//********************************************  ��������  **********************************************
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
	
	initialVariables(); //��ʼ������
	
	read();
	complement_graph();
	//read_without_e(); 
	//readMatrix(); 
	
	obtainAdjList();
	obtainVerDegree();
	
	initialVariablesRunTime(); //��ʼ������
	double proProduction;
	int vi = 0;
	int vj = 0;
	int indexMove = 0;
	int actionSizeZeroOrNot = 0;
	for( run=0; run<RunTime; run++ ) // ����RunTime�ζ���ʵ�� 
	{
		initialIteration(); //��ʼ��ÿ���ڵ㶼�ڽ⼯�У���ʼ��ÿ���ڵ����Ϊ�������� 
		
		iter = 0; //��������ָʾ�� 
		proProduction = 0.5; // �⼯�еĽڵ�ĸ��ʳ˻� 
		 
		start = clock();
		while( iter<Tmax && proProduction<Pmax ) //����������ֹ����ʱ����һֱ����
		{
			initialVariables_while(); 
			
			vi = chooseVertexRandomly(); // ���ѡ��һ���ڵ� 
			cover[vi] = 0; // ��vi�Ӹ��Ǽ����Ƴ�
			state[vi] = 1; // �ڵ�vi��ѡ�й��������ٴα����� 
			updateActionSet( vi );
			
			int actionSize = 1; // ���ڱ�����Ľڵ�Ŀ�ѡ����Ϊ����Ŀ 
			while( actionSize>0 )
			{
				vj = chooseAction( vi ); // �ڵ�vi��Ӧ���Զ���ѡ��һ����Ϊ 
				state[vj] = 1;
				updateActionSet( vj ); // ����vj���ھӵ���Ϊ���ϺͶ�Ӧ����Ϊ���� 
				
				// ��¼ÿһ��������Ľڵ���ѡ�����Ϊ�ı�� 
				indexMove = vertexCoverOrNot( vj );
				if( indexMove==1 ) // �����vj���ߺ������Ǹ��Ǽ�����vj��cover������
				{
					cover[vj] = 0; 
				} 
				else
				{
					cover[vj] = 1; // ����vj�Ծ��ڸ��Ǽ��� 
				}
				vi = vj; //��vj����vi�����µ���
				actionSizeZeroOrNot = checkActionSize( vi ); // �������ڵ����Ϊ��ĿΪ0�ˣ�����Զ���û�취��ѡ����Ϊ����һ�ֵ������� 
			    if( actionSizeZeroOrNot==0 ) // ��ѡ����Ϊ��Ŀ��Ϊ0
				{
					actionSize = 1; 
				} 
				else if( actionSizeZeroOrNot==1 )
				{
					actionSize = 0;
				}
			} 
			coverSize[iter] = computeCoverSize();
			computeDynamicThreshold( iter+1 ); //���������iter��ʱ�Ķ�̬��ֵ�����ڽ������߳ͷ� 
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
		solutionRunningTime[run] = runningTime; //ÿһ�����е�����ʱ�� 
		totalIterationTimes[run] = iter; // ÿ�����У��ܵ������� 
		solution[run] = cover; // ÿ�����У��õ��Ľ⼯
		solutionCardinality[run] = computeCoverSize(); 
	}
	
	// RunTime�����е�ʵ������ƽ�� 
	maxCardinality = findMaxCardinality(); // �ҵ����ֵ 
	maxCardinalityNumber = findMaxCardinalityNumber(); // ���ֵ���ֵĴ��� 
	minCardinality = findMinCardinality(); // �ҵ���Сֵ 
	minCardinalityNumber = findMinCardinalityNumber(); // ��Сֵ���ֵĴ��� 
	averageCardinality = computeAverageCardinality(); // ����ƽ��ֵ 
	stdCardinality = computeStdCardinality(); //�����׼�� 
	averageRunningTime = computeAverageRunningTime(); // ����ƽ������ʱ�� 
	averageIterationTimes = computeAverageIterationTimes(); // ����ƽ���������� 

	//���������ʵ���� 
	printResults();
	saveResults();
	
	return 0;
}

//***************  1  ��ȡ�ļ�������ıߵı�ʾ��  **************************
void read() // �õ��������ڽӾ��� �� ����¼�˱ߵľ���edgeMatrix[M][2] 
{
	int i;
	//int j;
	
	//FILE* fp = fopen("vertex6.txt","r");
	FILE* fp = fopen("brock200_2 (12).txt","r");
	//FILE* fp = fopen("frb30-15-1_450_17827.txt","r");
	
	if( !fp )
	{
		printf("�ļ��򿪴���");
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

//***************  1  ��ȡ�ļ�������ıߵı�ʾ��  **************************
void read_without_e() // �õ��������ڽӾ��� �� ����¼�˱ߵľ���edgeMatrix[M][2] 
{
	int i;
	//int j;
	
	FILE* fp = fopen("2000 25 70 ��1��.txt","r");
	
	if( !fp )
	{
		printf("�ļ��򿪴���");
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

//***************  2  ��ȡ�ڽӾ����ʾ������  **************************
void readMatrix()
{
	//int i;
	//int j;
	
	FILE* fp;
	
	fp = fopen( "ws2000��p=0.1��.txt" , "r" );
	
	if ( fp==NULL )
	{
		printf("�ļ���ʧ��");
		exit( 1 );
	}
	char C;
	int row=0;
	int col=0;
	int i1 = 0;//����matrix���±���Ҫÿ�ε���1����������������������������i1��j1
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

//***************************  5  ������Ĳ�ͼ  *****************************
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
void initialVariables() //��ʼ������
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
void initialVariablesRunTime() //��ʼ������
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

//************************************  6  �õ������ڽӱ�  ************************************
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
				adjList[i].push_back(j); //  �õ����ڽӱ��У�ÿһ���ڵ���ھӽڵ㶼�Ա�ŵ��������� 
			}
		}
	}
}

//********************************  7  �õ�����Ķ���Ϣ  *****************************
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
	maxdegree = max; // ���� 
	
	int min = deg[0];
	for( i=0; i<N; i++ )
	{
		if( min>deg[i] )
		{
			min = deg[i];
		}
	}
	mindegree = min; // ��С��  
	
	double sumdegree = 0;
	for( i=0; i<N; i++ )
	{
		sumdegree = sumdegree + deg[i];
	}
	avedegree = (double)( (double)sumdegree/ (double)N); // ƽ���� 
	
	edgenumber = (int)( sumdegree/ 2); // �ܱ��� 
}

//********************************  ÿ������ǰ�ĳ�ʼ��  ******** 
void initialIteration()
{
	int i;
	int j;
	for( i=0; i<N; i++ )
	{
		cover[i] = 1;
		state[i] = 3; //��ʼʱ�����нڵ㶼����δ����״̬�������Ա����� 
		actIndex[i] = N; // ��ʼʱ�����нڵ��ѡ�����Ϊ����Ϊ���N 
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
int chooseVertexRandomly() // ��N���ڵ������ѡ��һ����ʼ�ڵ� 
{
	//int i;
	//int j;
	
	int chosenIndex;
	chosenIndex = (int)(N * rand()) / (RAND_MAX+1);
	return chosenIndex;
} 

//********************************
int chooseAction( int vx ) // ������Ľڵ���Լ�����Ϊ�����У�������Ϊ����ѡ��һ����Ϊ 
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
	actIndex[vx] = maxIndex; // ��¼�ڵ�vxѡ�����Ϊ�ı�� 
	recordProbability.push_back( maxPro );
	return chosenVertex;
} 

//********************************
int moveOrNot( int vy ) // ���ڵ�vj����Ϊ���Ǽ����Ƴ����ж��Ƿ��Ǹ��Ǽ� 
{
	int i;
	int j;
	int index; // index=1,��ʾ�Ƴ�����Ȼ�Ǹ��Ǽ���vj�����Ƴ�������index=0, vj�������Ƴ�
	//cover[vy] = 0; //vj�Ƴ�ǰ�Ǹ��Ǽ�������ֻ��Ҫ�ж���vj�����ıߣ���vj�Ƴ����Ƿ��Ա����� 
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
		idx = 0; // ���е��ھ��У�ֻ��������һ���ھӲ��ڸ��Ǽ��У���������ھ�֮��ı߾Ͳ��ܱ����ǣ�
				 // ������ڵ㲻���Ƴ� 
	    //cover[vx] = 1;
	}
	else
	{
		idx = 1; // �ڵ�����Ƴ� 
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
		idx = 1; // vx�������ھӽڵ㶼��cover�У�����vx���Ƴ�������Ӱ��vx�ıߵĸ���״̬ 
	}
	else
	{
		idx = 0;
	}*/
	return idx;
}

//********************************
void updateActionSet( int vx ) // ������vi������δ��������Զ�������Ϊ����
{
	// vx�Ƴ��󣬽�vx�������Զ�������Ϊ�������Ƴ�
	// ��vx���ھӵ��ھ��У�ɾ��vx 
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
		//if( state[vxNeighbor]==3 )// ������״̬����û�б������
		//{
			//��vxNeighbor����Ϊ���У���vxɾ�� 
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
					vxPosition = j; // vx�����ھӵ���Ϊ���е�λ�� 
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
			
			//������Ϊ��������
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
int checkActionSize( int vx ) // �ж�vx�Ŀ�ѡ����Ϊ����Ŀ�Ƿ�Ϊ0�����Ϊ0��������ڵ㲻�����ٴ�ѡ����Ϊ 
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
	if( fail==adjList[vx].size() ) // �ڵ�vx�������ھӽڵ㶼�Ѿ������������ڵ�vxû�п�ѡ��Ϊ�� 
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
void computeDynamicThreshold( int it ) // ��������it��ʱ��0-it�ε�����ƽ��cover��С
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
void rewardProbabilityVertor() // ��������һ���У����б�����Ľڵ����Ϊ���� 
{
	int i;
	int j;
	int activatedVer;
	for( i=0; i<N; i++ )
	{
		if( state[i]==1 ) // �ڶ���״̬��������� 
		{
			activatedVer = i;
			for( j=0; j<action[activatedVer].size(); j++ )
			{
				//�ҵ���һ�ֵ����У�activatedVer��ѡ����Ϊ������Ϊ����ź�actIndex
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
		if( state[i]==1 ) // �ڶ���״̬���������������������Զ���ѡ�����ʲô��ΪҲ��Ҫ��¼ 
		{
			activatedVer = i;
			for( j=0; j<action[activatedVer].size(); j++ )
			{
				//�ҵ���һ�ֵ����У�activatedVer��ѡ����Ϊ������Ϊ����ź�actIndex
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
double computeProProduct() // ���㵱ǰ��������
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
				//�ҵ�coverVertex���ھ�ѡ��coverVertex�ĸ��� 
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
int computeCoverSize() // ����cover��1�ĸ���
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

//**********************************  26  ��ʵ�������ı���ʽ���д洢  ************************************
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

//*******************************  27  ������  ***************************************** 
void printResults()
{
	int i;
	int j;
	
	
	printf("*********************  ������ %d ��  *************************��\n\n",RunTime);
	
	printf("Network vertices = %d, run times = %d\n",N, RunTime);
	printf("a = %f, b = %f \n",a,b);
	printf("Tmax = %d, Pmax = %f \n\n",Tmax,Pmax);
	
	printf("1���õ��Ľ⼯��С�ֱ�Ϊ�� ");
	for( i=0; i<RunTime; i++ )
	{
		printf("%d ",solutionCardinality[i]);
	}
	printf("\n\n");
	
	printf("2���⼯��С��ƽ��ֵΪ��%f����׼��Ϊ��%f\n\n", averageCardinality, stdCardinality);
	
	printf("3��ƽ������ʱ��Ϊ��%f, ƽ����������Ϊ��%f \n\n", averageRunningTime, averageIterationTimes);
	
	printf("4���⼯��С��СֵΪ��%d, ȡ����Сֵ�Ĵ���Ϊ��%d\n\n", minCardinality, minCardinalityNumber);
	
	printf("5���⼯��С���ֵΪ��%d, ȡ�����ֵ�Ĵ���Ϊ��%d\n\n", maxCardinality, maxCardinalityNumber);
	
/*	printf("6���õ��Ľ⼯�е�Ԫ�طֱ�Ϊ��\n");
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












