/* Apriori algorithm */

#include <stdio.h>
#include <vector>
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <set>
#include <iterator>
#include <utility>
#include <map>
#include <cmath>
#include <cstring>
#include <list>

using namespace std;

#define MAX 10000
FILE *fp2;

map<string, int> array;			         //for 1-itemset support

int x,sum;
int maxsize;
int support;
float conf;

map <set<string>, int> prev_f;			//for itemsets of size greater than 1 
map <set<string>, int> curr;

struct hash_node{
    hash_node *right;
    hash_node *left;
    vector< pair< set<string>, int > > elem;
};

struct hash_node *root;
struct Candidate
{
    vector< set<string> > csets;		//to store candidate itemsets
};

struct Frequent
{
    vector< set<string> > fsets;	//to store frequent itemsets
};

Candidate C[MAX];
Frequent L[MAX];

vector < set<string> > Database;		//contains all transactions

int min_sup;

vector<set<string> > vec_sub;		

int conv_str(string str){
    int i;
    sum = 0;
    for(i=0;i<str.size();i++){
           sum += str[i]%27;            
    }
    return sum;
}

/* Write rules into file*/
void print_set(set<string> s){
    set<string>::iterator it;
    fputs("{", fp2);
    for(it = s.begin(); it != s.end(); it++)
    {
    fputs((*it).c_str(),fp2);
    fputs(",",fp2);   
    }
    fputs("}",fp2);
}

void print( list<string> l){
    set<string> s;
    for(list<string>::iterator it=l.begin(); it!=l.end() ; ++it)
        s.insert(*it);
    vec_sub.push_back(s);
}

/* Generate rule based on Support and Confidence */
void Rule_gen(vector<string> st){
    unsigned int pow_set_size = pow(2, st.size());
    int counter, j;
    for(counter = 0; counter < pow_set_size; counter++)
    {
        vector<string> new_set;
        for(j = 0; j < st.size(); j++)
        {
            if(counter & (1<<j))
                new_set.push_back(st[j]);
        }
        if(new_set.size() > 0 && new_set.size() < st.size()){
            set<string> s(new_set.begin(), new_set.end() );
            map<set<string>,int >::iterator it;
            if((it = prev_f.find(s)) != prev_f.end()){
                float s_old = it->second;
                float s_new = prev_f[set<string>(st.begin(),st.end())];
                float con = s_new/s_old;
                cout<<"s_old "<<s_old<<endl<<"s_new "<<s_new<<endl<<"con "<<con<<endl;
                if(con >= conf){
                    print_set(s);
                    vector<string> diff(20);
                    vector<string>::iterator it2;
                    it2 = set_difference(st.begin(), st.end(), s.begin(), s.end(), diff.begin());
                    diff.resize(it2 - diff.begin());
                    fputs(" --> ",fp2);
                    print_set(set<string>(diff.begin(),diff.end()));
                    fputs("\n",fp2);
                }
            }
        }
    }
}

/* Generate subset from transactions */
void subset(vector<string> arr, int size, int left, int index, list<string> &l){    
    if(left==0){
        print(l);
        return;
    }
    for(int i=index; i<size;i++){
        l.push_back(arr[i]);
        subset(arr,size,left-1,i+1,l);
        l.pop_back();
    }

}

/*count support using hash tree */
void Lookup(hash_node *root, set<string> sub, int k){

    if(sub.size() != k)
        cout<<"Not subset of size k ";
    hash_node *temp = root;
    hash_node *prev = root;
    int level=0;
    set<string>::iterator it = sub.begin();
    while(temp != NULL){

        level++;
        if(it != sub.end() && (conv_str(*it))%2 == 0){
            prev = temp;
            temp = temp->left;
            
        }else{
            prev = temp;
            temp = temp->right;
        }
        it++;
 
    }

    vector< pair<set<string>,int> > v = prev->elem;
    vector< pair<set<string>, int> >::iterator it_v;
    
    for(it_v = v.begin(); it_v != v.end(); it_v++){
        vector<string> s;
        vector<string>::iterator it_vv;
        vector<string> big((it_v->first).begin(), (it_v->first).end());
        vector<string> small(sub.begin(), sub.end());

        set_intersection(big.begin(), big.end(), small.begin(), small.end(), back_inserter(s));
        if(s.size() == k){
        curr[it_v->first]++; 
            if(curr[it_v->first] >= support && prev_f.find(sub) == prev_f.end()){
                    L[k-1].fsets.push_back(sub);
                    prev_f.insert(make_pair(it_v->first,curr[it_v->first]));
                    Rule_gen(vector<string>(sub.begin(), sub.end()));
                
            }else if(prev_f.find(sub) != prev_f.end()){
                      prev_f[it_v->first] = curr[it_v->first];
            }
        }
    }
}

/* store candidate itemset into hash tree */
void insert(hash_node *root, int k, set<string> cand){
    //find the leaf
    hash_node *temp = root;
    hash_node *prev = root;

    int level=0;
    set<string>::iterator it = cand.begin();
    while(temp != NULL){
        level++;
        if(it != cand.end())
            x = conv_str(*it);
        if(x%2 == 0){
            prev = temp;
            temp = temp->left;
        }else{
            prev = temp;
            temp = temp->right;
        }
        it++;
    }
    curr.insert(make_pair(cand,0));
    if(level == k+1){		//if depth has reached depth K+1 then store there anyway
        (prev->elem).push_back(make_pair(cand, 0));
        }
    if(level < k+1){		//if less than k+1 then
        if((prev->elem).size() < maxsize){	//store only if no. of itemset stored is less than maximum size
            prev->elem.push_back(make_pair(cand,0));
        }else{				//size less than k+1 and no. of itemset stored is greater than or equal to maximum size
            prev->left = new hash_node;
            prev->left->right = NULL;
            prev->left->left = NULL;
            prev->right = new hash_node;
            prev->right->right = NULL;
            prev->right->left = NULL;
            vector<set<string> > v;
            vector<pair<set<string>, int > >::iterator it_f;
            for(it_f = prev->elem.begin(); it_f != prev->elem.end(); it_f++)
            {
                v.push_back(it_f->first);
            }
            v.push_back(cand);
    
            vector<set<string> >::iterator it_v;
            for(it_v = v.begin(); it_v != v.end(); it_v++){
                set<string>::iterator it_s = (*it_v).begin();
                advance(it_s, level-1);
                if(conv_str((*it_s))%2 == 0)
                {
                    prev->left->elem.push_back(make_pair((*it_v),0));

                }

                else{
                    prev->right->elem.push_back(make_pair((*it_v),0));
                }
            }
        }
    }
}
/* Generate candidate itemset using F(k-1)*F(k-1)*/
bool checkJoinAbility( set<string> a, set<string> b)
{

    set<string>::iterator it(a.begin());
    std::advance(it,b.size()-1);
    if(std::equal(a.begin(),it,b.begin()))
        return true;
    return false;

}

/*Generate candidate item set */
Candidate apriori_gen(Frequent fr)
{

    int i,j;
    Candidate cd;
    vector < set<string> > l1 = fr.fsets;
    vector < set<string> > l2 = fr.fsets;

    for(i = 0; i< l1.size(); i++)
    {
        for(j = i+1; j < l2.size(); j++)
        {
            set < string > sj;
            if(l1[i].size() == 1)		//joining two single sets anyway
            {

                set<string>::iterator it;
                it = l1[i].begin();
                sj.insert(*it);
                it = l2[j].begin();
                sj.insert(*it);
                cd.csets.push_back(sj);

            }
            else						//when itemset size is greater than 1
            {

                if(checkJoinAbility(l1[i], l2[j]))
                {

                    set<string>::iterator it;

                    for(set<string> :: iterator it = l1[i].begin(); it != l1[i].end(); ++it)
                    {
                        sj.insert(*it);
                    }
                    for(set<string> :: iterator it = l2[j].begin(); it != l2[j].end(); ++it)
                    {
                        sj.insert(*it);
                    }
                    cd.csets.push_back(sj);

                }

            }

        }

    }

    return cd;
}

/*Generate candidate item set */
void apriori()
{
    int k;
    int i;
    for(k = 1; k < 20; k++)
    {
        C[k] = apriori_gen(L[k-1]);
        vector<set<string> >::iterator it;
        root = new hash_node;
        root->left = new hash_node;
        root->right = new hash_node;
        root->left->left = NULL;    root->left->right = NULL;
        root->right->right = NULL;  root->right->left = NULL;
        for(it = C[k].csets.begin(); it != C[k].csets.end(); it++ ){
            insert(root,k+1,*it);
        }
        for( it = Database.begin(); it != Database.end(); it++ ){
            vec_sub.clear();
            list<string> lt;
            vector<string> v(it->begin(), it->end());
            subset(v, v.size(), k+1,0, lt);			//vec_sub contain all subset of transactions pointed by it
            for(i = 0;i < vec_sub.size(); i++){     //find all subset count in hash tree
                Lookup(root, vec_sub[i], k+1);   
            }
        }
        delete root;

    }
}

/*Main function */
int main()
{
    FILE *fp;
    char buf[1000];
    support =50;
    conf =0.3;
    fp = fopen("groceries.csv","r");
    fp2 = fopen("output.txt","a+");
    while(fgets(buf, sizeof(buf), fp))
    {
        set < string > db;
        db.clear();
        char *ch;
        ch = strtok(buf,",\n"); 
        while(ch != NULL)
        {
        	//inserting transcations into database
            db.insert(string(ch));
            set<string> s;
            s.insert(string(ch));
            map<set<string>, int> :: iterator it;

            if(array.find(string(ch)) == array.end())
            {
                array.insert(make_pair(string(ch), 0));
            }
            else {
                array[string(ch)] += 1;
                if(array[string(ch)] >= support){
                    if((it = prev_f.find(s)) != prev_f.end()){
                        it->second = array[string(ch)];
                    }else{
                        prev_f.insert(make_pair(s,array[string(ch)]));
                    }
                }

            }
            ch = strtok(NULL,",\n");
            s.clear();
        }
        Database.push_back(db);

    }
        map<set<string>, int > :: iterator it_m;
        for( it_m = prev_f.begin(); it_m != prev_f.end(); it_m++){
            L[0].fsets.push_back(it_m->first);
        }
    apriori();
    fclose(fp);
    return 0;
}