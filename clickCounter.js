function reset_counter() {
    localStorage.clickcount = 0;
    document.getElementById("result").innerHTML = "You have clicked the button " + localStorage.clickcount + " time(s).";
  }
  
  document.getElementById('reset').addEventListener('click', reset_counter);
  document.getElementById("result").innerHTML = "You have clicked the button " + (localStorage.clickcount || 0) + " time(s).";