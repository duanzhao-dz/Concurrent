typedef unsigned long int pthread_t;
pthread_t id1,id2;
int i;
int j;
void t1(){
  i=i+j;
  i=i+j;
}
void t2(){
  j=j+i;
  j=j+i;
}
int main(){
	i=1;
	j=1;
  pthread_create(&id1,0,t1,0);
  pthread_create(&id2,0,t2,0);
  
  pthread_join(id1,0);
  pthread_join(id2,0);
  
  if(j>8){
	 goto ERROR;
     ERROR: return 0;
  }
  return 0;
}
