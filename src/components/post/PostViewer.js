import React from "react";
import { useEffect, useState,useContext } from "react";

import axios from "axios";
import { BlogContext } from "../context/blog-context";

import SinglePost from "./Post";
import { CircularProgress } from "@mui/material";
export const PostViewer = ({to}) => {
  const ctx=useContext(BlogContext)
 
  const postID = window.location.href.split(to)[1];
  const [postData, setPostData] = useState({ status: "loading" });
  const [authorData, setAuthorData] = useState({ status: "loading" });
 console.log(ctx)
  useEffect(() => {
    async function makereq(){
      try {
        const postRes = await axios.get(`http://localhost:5000/api/posts/${postID}`,{headers:{ "Authorization":`${ctx.key} ${ctx.id}` }});
        const post = postRes.data.post;
        setPostData({ status: "done", post });
        const authorRes = await axios.get(`http://localhost:5000/api/authors/${post.author}`,{headers:{ "Authorization":`${ctx.key} ${ctx.id}`}});
        const author = authorRes.data;
        setAuthorData({ status: "done", author });
      } catch (error) {
        console.log(error);
        setPostData({ status: "error", message: error.message });
      }
    }
    makereq()
 
  }, [postID]);

  if (postData.status === "loading" || authorData.status === "loading") {
    return <center><CircularProgress/></center>;
  }

  if (postData.status === "error" || authorData.status === "error") {
    return <center><CircularProgress/></center>;
  }

  return (
    <SinglePost
      postID={postID}
      title={postData.post.title}
      subtitle={postData.post.subtitle}
      content={JSON.parse(postData.post.content)}
      author={authorData.author.name}
      likes={postData.post.likes}
      tags={postData.post.tags}
      date={postData.post.Date}
      authorpic={authorData.author.image}
    />
  );
};


