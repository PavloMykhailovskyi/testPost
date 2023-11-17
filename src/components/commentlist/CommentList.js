import React from "react";
import { useState, useEffect,useContext } from "react";
import axios from "axios";

import Comment from "./Comment";
import useMediaQuery from "@mui/material/useMediaQuery";
import Box from "@mui/material/Box";
import { Button, Divider, TextField } from "@mui/material";

import { BlogContext } from "../context/blog-context";

const CommentList = ({ postID }) => {
  const ctx=useContext(BlogContext)
 
  const matches = useMediaQuery("(max-width:600px)");
  const [name,setName]=useState("")
  const [email,setEmail]=useState("")
  const [comment,setComment]=useState("")
  const [commentData, setCommentData] = useState({
    status: "loading",
    comments: [
      {
        name: "loading username",
        email: "loading@loading.com",
        comment: "loading comment...",
      },
    ],
  });

  useEffect(() => {
  async function  makereq(){
    try {
      const res = await axios.get(`http://localhost:5000/api/comments/post/${postID}`,{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
      setCommentData({ status: "done", comments: res.data.comments });
    } catch (error) {
      console.error(error);
    }
    }
   makereq()
  }, [postID]);

  const postComment=async()=>{
    let msg="";
    if(name.length==0){
       msg+="Name"
       alert("Empty Fields - "+msg)
       return
    }
    if(email.length==0){
      msg+="Email"
      alert("Empty Fields - "+msg)
      return
   }
   if(comment.length==0){
    msg+="Comment"
    alert("Empty Fields - "+msg)
    return
 }
    const commentObject = {
      name:name,
      email:email,
      comment: comment,
      post: postID,
   
    };
    setName("")
    setEmail("")
    setComment("")
    try {
      const res = await axios.post("http://localhost:5000/api/comments/", commentObject,{headers:{ "Authorization": `${ctx.key} ${ctx.id}`}});
      console.log(res);
      
      setCommentData(prev=>({ status: "done", comments: [...prev.comments,commentObject] }));
    } catch (error) {
      alert(error)
    }

  }

  return (
    
    <Box
      sx={{
        display: "flex",
        alignItems: "stretch",
        width: "100%",
        flexDirection: "column",
        gap: 2,
      }}
    >
        <Box
      sx={{
        display: "flex",
        alignItems: "stretch",
        width: "100%",
        flexDirection: "row",
        gap: 2,
      }}
    >
     <TextField
      label="Name"
      sx={{width:"50%"}}
      value={name}
     
      onChange={(e)=>{setName(e.target.value)}}
      />
         <TextField
      label="Email"
      sx={{width:"50%"}}
      value={email}
      onChange={(e)=>{setEmail(e.target.value)}}
      /><br/>
    </Box>
    <TextField
      label="Comment"
      value={comment}
      onChange={(e)=>{setComment(e.target.value)}}
      fullWidth
      multiline
      minRows={3}
      />  
     <Button onClick={postComment} color="success" sx={{width:matches?"100%":"20%"}} variant="outlined">
       Comment
     </Button>
     <Divider/>
      {commentData.comments.length==0 && <span style={{color:"grey",fontSize:"1em"}}>No Comments Yet , Be the First To Comment</span>}
      {commentData.comments.slice(0).reverse().map((comment) => (
        <Comment {...comment} key={comment._id || ""} />
      ))}
    </Box>
  );
};

export default CommentList;
