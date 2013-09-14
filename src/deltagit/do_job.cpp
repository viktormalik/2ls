/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>
#include <iostream>
#include <fstream>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "job_status.h"
#include "do_job.h"

/*******************************************************************\

Function: check_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void check_out(job_statust &job_status)
{
  const std::string working_dir=job_status.id+".wd";

  std::string command;

  // Do a shared clone -- this uses very little disc space.
  // Will overwrite log.
  command="git clone --no-checkout --shared source-repo "+
          working_dir+
          " 2>&1 > "+job_status.id+".log";

  int result1=system(command.c_str());
  if(result1!=0)
  {
    job_status.failure=true;
    job_status.write();
    return;
  }
  
  // Now do checkout; this will eat disc space.
  command="cd "+working_dir+"; "+
          "git checkout --detach "+job_status.commit+
          " 2>&1 >> "+job_status.id+".log";

  int result2=system(command.c_str());

  if(result2!=0)
  {
    job_status.failure=true;
    job_status.write();
    return;
  }

  job_status.status=job_statust::BUILD;
  job_status.write();  
}

/*******************************************************************\

Function: build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build(job_statust &job_status)
{
  const std::string working_dir=job_status.id+".wd";
  
  std::string command;

  // Now run build script in working directory.
  command="cd "+working_dir+"; ../build"+
          " 2>&1 >> "+job_status.id+".log";

  int result=system(command.c_str());
  
  if(result!=0)
  {
    job_status.failure=true;
    job_status.write();
    return;
  }

  job_status.status=job_statust::ANALYSE;
  job_status.write();  
}

/*******************************************************************\

Function: analyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void analyse(
  job_statust &job_status,
  const std::list<job_statust> &jobs)
{
  // get the job before this one

  std::string previous="";

  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->id==job_status.id) break;
    previous=j_it->id;
  }
  
  if(previous!="")
    std::cout << "Differential analysis between "
              << previous << " and " << job_status.id
              << "\n";
  else
    std::cout << "One-version analysis for " << job_status.id
              << "\n";

  job_status.failure=true;
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(job_statust &job_status,
            const std::list<job_statust> &jobs)
{
  while(job_status.status!=job_statust::DONE &&
        !job_status.failure)
  {
    switch(job_status.status)
    {
    case job_statust::INIT: return; // done by deltagit init
    case job_statust::CHECK_OUT: check_out(job_status); break;
    case job_statust::BUILD: build(job_status); break;
    case job_statust::ANALYSE: analyse(job_status, jobs); break;
    case job_statust::DONE: break;
    }
  }

}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(const std::string &id)
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);

  // get current job status
  job_statust job_status(id);
  do_job(job_status, jobs);
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // do jobs that need work
  for(std::list<job_statust>::iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->status!=job_statust::DONE &&
       !j_it->failure)
    {
      std::cout << "Job " << j_it->id << std::endl;
      do_job(*j_it, jobs);
    }
  }
}

