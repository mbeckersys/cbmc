/*******************************************************************\

Module: Dump flowchart

Author: Martin Becker, becker@rcs.ei.tum.de

\*******************************************************************/

#ifndef CPROVER_FLOWCHART_H
#define CPROVER_FLOWCHART_H

#include <goto-programs/goto_functions.h>

void flowchart(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out,
  bool make_bb);

#endif
