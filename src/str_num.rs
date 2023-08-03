use std::error::Error;

fn box_dyn_error(s: &str) -> Box<dyn Error> {
    let err: Box<dyn Error> = String::from(s).into();
    err
}

// pub fn starts_with_minus (s: &str) -> bool {
//     let string_bytes = s.as_bytes();
//     string_bytes[0] == b'-'
// }

fn is_number (s: &str) -> bool {
    let string_bytes = s.as_bytes();
    let allowed_bytes = (".0123456789").as_bytes();
    let mut start_index = 0;
    if string_bytes[0] == b'-'{
        start_index = 1
    }
    let mut decs = 0;
    for &v in string_bytes[start_index..].iter(){
      if v == b'.'{
        decs += 1;
        if decs > 1{
          return false
        }
        continue;
      }
      for (j, &w) in allowed_bytes.iter().enumerate() {
        if v==w{
          break;
        }
        if j == allowed_bytes.len()-1{
          return false
        }
      }
  }
    true
}

pub fn mdp(s: &str, places: i32) -> Result<String, Box<dyn Error>> {
    if !is_number(s){
        return Err(box_dyn_error("not a number"))
    }
    let (neg, abs_val_bytes) = {
        let all_bytes = s.as_bytes();
        let neg = if all_bytes[0] == b'-' {true} else {false};
        let bytes = if neg {
            &all_bytes[1..]
        } else {
            all_bytes
        };
        (neg, bytes)
    };
    let mut zero = true;
    for &v in abs_val_bytes.iter(){
      if (v != b'0') & (v != b'.'){
        zero = false;
        break;
      }
    }
    if zero {
      return Ok(String::from("0"))
    }
    let dec_index;
    match abs_val_bytes.iter().position(|&x| x == b'.') {
        None => dec_index = abs_val_bytes.len(),
        Some(ind) => dec_index = ind,
    }

    let before_ind = &abs_val_bytes[..dec_index];

    let after_ind;
    if dec_index == abs_val_bytes.len() {
        after_ind = "0".as_bytes();
    } else {
        after_ind = &abs_val_bytes[dec_index+1..];
    }

    let mut v: Vec<u8> = vec![];
    if places > 0 {
        v.extend(before_ind);
        v.extend(after_ind);
        let new_index = dec_index + places as usize;
        if new_index >= v.len() {
            let needed_zeros = (new_index - v.len()) + 1;
            let zeros: Vec<u8> = vec![b'0'; needed_zeros];
            v.extend(zeros)
        }
        v.insert(new_index, b'.')
    } else if places < 0 {
        let abs_places = -places as usize;
        if abs_places < before_ind.len() {
            v.extend(before_ind);
            v.extend(after_ind);
            let new_index = before_ind.len() - abs_places;
            v.insert(new_index, b'.');
        } else {
            let needed_zeros = (abs_places - before_ind.len()) + 1;
            let zeros: Vec<u8> = vec![b'0'; needed_zeros];
            v.extend(zeros);
            v.extend(before_ind);
            v.extend(after_ind);
            v.insert(1, b'.');
        }
    } else {
        v.extend(before_ind);
        v.extend(after_ind);
        v.insert(dec_index, b'.');
    }
    while v[v.len()-1] == b'0' && v[v.len()-2] != b'.'{
        v = v[..v.len()-1].to_vec();
    }
    if v[v.len()-1] == b'0' && v[v.len()-2] == b'.' {
        v = v[..v.len()-2].to_vec();
    }
    while v[0] == b'0' && v[1] != b'.'{
        v = v[1..].to_vec();
    }
    if neg {
        v.insert(0, b'-')
    }
    let res = std::str::from_utf8(&v)?;
    return Ok(String::from(res))
}

pub fn without_e_notation (s: &str) -> Result<String, Box<dyn Error>> {
    
    let parts: Vec<&str> = s.split("E").collect();
    let res = if parts.len() == 1 {
        if !is_number(&s) {
            Err(box_dyn_error("not a number"))
        } else {
            Ok(s.to_string())
        }
    } else if parts.len() == 2 {
        let places: i32 = parts[1].parse()?;
        let inner = mdp(parts[0], places)?; 
        Ok(inner)
          
    } else {
        Err(box_dyn_error("multiple Es"))
    };
    res
}

pub fn dec_to_rat(s: &str)->Result<String, Box<dyn Error>>{
    if !is_number(s){
        return Err(box_dyn_error("can't change non-number to rational"));
    }
    let dec_index;
    match s.find('.'){
        Some(ind) => dec_index = ind,
        None => {
            let mut res = String::from(s);
            res.push_str("/1");
            return Ok(res)
        },
    }
    let mut num = String::from(s);
    num.remove(dec_index);
    let zeros = s.len() - (dec_index+1);
    let den = String::from("1") + &"0".repeat(zeros);
    Ok(String::new() + &num + "/" + &den)
}

pub fn truncate (value: &str, places: usize) -> Result<String, Box<dyn Error>> {
    if !is_number(value){
        return Err(box_dyn_error("can't change non-number to rational"));
    }
    let dec_index;
    match value.find('.'){
        Some(ind) => dec_index = ind,
        None => {
            return Ok(String::from(value))
        },
    }
    let to_add = if places == 0 {
        0
    } else {
        places + 1
    };
    if dec_index + to_add > value.len() {
        return Ok(String::from(value))
    };
    Ok(String::from(&value[..dec_index + to_add]))
}

pub fn get_decimal_places (value: &str) -> Result<usize, Box<dyn Error>> {
    if !is_number(value){
        return Err(box_dyn_error("can't get decimal places of non-number"));
    }
    let places = match value.find('.'){
        Some(ind) => {
            value[ind+1..].len()
        },
        None => {
            0
        },
    };
    Ok(places)
}


