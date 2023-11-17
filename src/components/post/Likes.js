import React from "react";
import {Button} from "@mui/material";
import FavoriteIcon from "@mui/icons-material/Favorite";
import FavoriteBorderIcon from '@mui/icons-material/FavoriteBorder';
import axios from "axios";
import { useState,useEffect,useContext } from "react";
import { BlogContext } from "../context/blog-context";

const Likes=({postid,count})=>{
  const ctx=useContext(BlogContext)
 
    const [liked,setLiked]=useState(false)
    const [counter,setCounter]=useState(count)
    
useEffect(()=>{
    const likes=localStorage.getItem("likes");
    if(likes==null){
        localStorage.setItem("likes", "none");
    }else{
       if(likes.split(",").includes(postid)){
           setLiked(true)
       }
    }
},[])
    
    const onLike=async()=>{
        let currentlikes=localStorage.getItem("likes")
        if(currentlikes==null){
            localStorage.setItem("likes", postid.toString());
            setLiked(true)
            setCounter(counter+1)
        }
        if(liked){

          let newlikes=currentlikes.split(",").filter(el => el !== postid)
          if(newlikes.length==0){
            localStorage.setItem("likes", "none");
          }else{
            localStorage.setItem("likes", newlikes.toString());
          }
          setLiked(false)
          
         if(counter>0) setCounter(counter-1)
        }else{
            if(currentlikes==="none"){
                localStorage.setItem("likes", postid.toString());
            }else{
                let newlikes2=currentlikes.split(",")
                newlikes2[newlikes2.length]=postid
               localStorage.setItem("likes", newlikes2.toString());
            }
         
           setLiked(true)
           setCounter(counter+1)
        }
      
        try {
            const res = await axios.patch("http://localhost:5000/api/posts/likes/update", {postId:postid,like:!liked},{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
            
          } catch (error) {
            alert(error)
          }


    }
         
    return(
        <Button
        sx={{color:"blue"}}
        size="large"
        color="inherit"
        endIcon={liked?<FavoriteIcon sx={{color:"red"}} />:<FavoriteBorderIcon/>}
        onClick={onLike}
      >
       {counter}
      </Button>
    )

}

export default Likes;