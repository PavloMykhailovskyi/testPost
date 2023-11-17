import React from "react";
import { Avatar, CardHeader, Divider } from "@mui/material";
import Card from "@mui/material/Card";
import CardContent from "@mui/material/CardContent";

const Comment = ({ name, email, comment }) => {
  return (
    <Card variant="outlined">
      <CardHeader
        avatar={<Avatar>{name[0]}</Avatar>}
        title={name}
        subheader={email}
      />
      <Divider />
      <CardContent>{comment}</CardContent>
    </Card>
  );
};

export default Comment;
