pthread_t id1,id2;
int i;
int j;

int main(){
  pthread_create(&id1,0,t1,0);
  pthread_create(&id1,0,t2,0);
  
  pthread_join(id1,0);
  pthread_join(id2,0);
  
  if(j>8){
     ERROR: return 0;
  }
  return 0;
}